#define _GNU_SOURCE
#include "forge_web.h"
#include <arpa/inet.h>
#include <ctype.h>
#include <curl/curl.h>
#include <errno.h>
#include <fcntl.h>
#include <json-c/json.h>
#include <limits.h>
#include <math.h>
#include <microhttpd.h>
#include <openssl/crypto.h>
#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <openssl/rand.h>
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>

#define H(p) ((int64_t)(intptr_t)(p))
#define P(t, h) ((t *)(intptr_t)(h))
#define BODY_MAX (25u * 1024u * 1024u)
#define JSON_MAX (2u * 1024u * 1024u)
#define FILE_MAX (20u * 1024u * 1024u)
#define FETCH_MAX (4u * 1024u * 1024u)
/* Cache at most sixteen small tracking blocks per worker (about 33 KiB).
 * Larger scopes release excess blocks at scope end; thread teardown releases
 * the cache and any resources left by an early return. */
#define OWNED_BLOCK_SIZE 128u
typedef struct {
  void *value;
  int json;
} Owned;
typedef struct OwnedBlock {
  struct OwnedBlock *previous;
  size_t used;
  Owned values[OWNED_BLOCK_SIZE];
} OwnedBlock;
typedef struct {
  OwnedBlock first;
  OwnedBlock *current, *available;
  unsigned cached;
  CURL *curl;
} ThreadState;
static _Thread_local ThreadState *thread_state;
static pthread_key_t state_key;
static pthread_once_t state_once = PTHREAD_ONCE_INIT;
static int state_key_ok;
static void clear_scope(ThreadState *s) {
  OwnedBlock *b = s->current;
  while (b) {
    while (b->used) {
      Owned *o = &b->values[--b->used];
      if (o->json)
        json_object_put(o->value);
      else
        free(o->value);
    }
    OwnedBlock *previous = b->previous;
    if (b != &s->first) {
      if (s->cached < 15) {
        b->previous = s->available;
        s->available = b;
        s->cached++;
      } else
        free(b);
    }
    b = previous;
  }
  s->current = &s->first;
}
static void destroy_state(void *value) {
  ThreadState *s = value;
  if (!s)
    return;
  clear_scope(s);
  while (s->available) {
    OwnedBlock *b = s->available;
    s->available = b->previous;
    free(b);
  }
  if (s->curl)
    curl_easy_cleanup(s->curl);
  thread_state = NULL;
  free(s);
}
static void make_state_key(void) {
  state_key_ok = pthread_key_create(&state_key, destroy_state) == 0;
}
static ThreadState *get_state(void) {
  if (thread_state)
    return thread_state;
  pthread_once(&state_once, make_state_key);
  if (!state_key_ok)
    return NULL;
  ThreadState *s = calloc(1, sizeof(*s));
  if (!s)
    return NULL;
  s->current = &s->first;
  if (pthread_setspecific(state_key, s)) {
    free(s);
    return NULL;
  }
  thread_state = s;
  return s;
}
static void *track(void *value, int json) {
  if (!value)
    return NULL;
  ThreadState *s = get_state();
  if (s && s->current->used == OWNED_BLOCK_SIZE) {
    OwnedBlock *b = s->available;
    if (b) {
      s->available = b->previous;
      s->cached--;
    } else
      b = calloc(1, sizeof(*b));
    if (b) {
      b->previous = s->current;
      s->current = b;
    } else
      s = NULL;
  }
  if (!s) {
    if (json)
      json_object_put(value);
    else
      free(value);
    return NULL;
  }
  s->current->values[s->current->used++] = (Owned){value, json};
  return value;
}
static const char *copy(const char *s) { return track(strdup(s ? s : ""), 0); }
int64_t fw_scope_begin(void) { return fw_scope_end(); }
int64_t fw_scope_end(void) {
  if (thread_state)
    clear_scope(thread_state);
  return 1;
}
static pthread_once_t curl_once = PTHREAD_ONCE_INIT;
static int curl_ready;
static void init_curl(void) {
  curl_ready = curl_global_init(CURL_GLOBAL_DEFAULT) == CURLE_OK;
}
static CURL *get_curl(void) {
  pthread_once(&curl_once, init_curl);
  if (!curl_ready)
    return NULL;
  ThreadState *s = get_state();
  if (!s)
    return NULL;
  if (!s->curl)
    s->curl = curl_easy_init();
  if (s->curl)
    curl_easy_reset(s->curl);
  return s->curl;
}
const char *fw_env(const char *name, const char *fallback) {
  const char *s = getenv(name);
  return s ? s : fallback;
}
/* json-c intentionally replaces duplicate object members and accepts strings
 * containing an escaped NUL. Forge string/FFI APIs are NUL-terminated, so those
 * representations cannot safely reach application authorization/SQL policy.
 * Run this bounded lexical pass only after the strict parser validated syntax.
 * Object-local key sets compare decoded names, including escaped equivalents.
 */
static int json_unambiguous(const char *text, size_t size) {
  struct {
    struct json_object *keys;
    int key_next;
  } frames[32] = {0};
  unsigned depth = 0;
  const char *p = text, *end = text + size;
  struct json_tokener *key_tok = NULL;
  int ok = 1;
  while (ok && p < end) {
    if (*p == '{' || *p == '[') {
      if (depth == sizeof(frames) / sizeof(frames[0])) {
        ok = 0;
        break;
      }
      frames[depth].keys = *p == '{' ? json_object_new_object() : NULL;
      frames[depth].key_next = *p == '{';
      if (*p == '{' && !frames[depth].keys) {
        ok = 0;
        break;
      }
      depth++;
      p++;
    } else if (*p == '}' || *p == ']') {
      if (!depth) {
        ok = 0;
        break;
      }
      if (frames[--depth].keys)
        json_object_put(frames[depth].keys);
      frames[depth].keys = NULL;
      p++;
    } else if (*p == ',') {
      if (depth && frames[depth - 1].keys)
        frames[depth - 1].key_next = 1;
      p++;
    } else if (*p == '"') {
      const char *begin = p++;
      int escaped = 0;
      while (p < end && *p != '"') {
        unsigned char byte = (unsigned char)*p++;
        if (byte < 0x20) {
          ok = 0;
          break;
        }
        if (byte == '\\') {
          escaped = 1;
          if (p == end) {
            ok = 0;
            break;
          }
          if (*p == 'u') {
            if (end - p < 5 || !memcmp(p + 1, "0000", 4)) {
              ok = 0;
              break;
            }
            p += 5;
          } else
            p++;
        }
      }
      if (!ok || p == end) {
        ok = 0;
        break;
      }
      p++;
      if (depth && frames[depth - 1].keys && frames[depth - 1].key_next) {
        char short_key[256], *allocated = NULL;
        struct json_object *decoded = NULL;
        const char *key = short_key;
        if (escaped) {
          if (!key_tok)
            key_tok = json_tokener_new_ex(2);
          if (!key_tok) {
            ok = 0;
            break;
          }
          json_tokener_reset(key_tok);
          decoded = json_tokener_parse_ex(key_tok, begin, (int)(p - begin));
          if (!decoded ||
              json_tokener_get_error(key_tok) != json_tokener_success) {
            if (decoded)
              json_object_put(decoded);
            ok = 0;
            break;
          }
          key = json_object_get_string(decoded);
        } else {
          size_t length = (size_t)(p - begin) - 2;
          if (length < sizeof(short_key)) {
            memcpy(short_key, begin + 1, length);
            short_key[length] = 0;
          } else {
            allocated = strndup(begin + 1, length);
            key = allocated;
          }
        }
        struct json_object *unused;
        if (!key ||
            json_object_object_get_ex(frames[depth - 1].keys, key, &unused) ||
            json_object_object_add(frames[depth - 1].keys, key, NULL))
          ok = 0;
        free(allocated);
        if (decoded)
          json_object_put(decoded);
        frames[depth - 1].key_next = 0;
      }
    } else if (*p == '-' || isdigit((unsigned char)*p)) {
      const char *begin = p;
      int floating = 0;
      while (p < end && (*p == '-' || *p == '+' || *p == '.' || *p == 'e' ||
                         *p == 'E' || isdigit((unsigned char)*p))) {
        if (*p == '.' || *p == 'e' || *p == 'E')
          floating = 1;
        p++;
      }
      errno = 0;
      char *number_end;
      if (floating) {
        double value = strtod(begin, &number_end);
        if (!isfinite(value))
          ok = 0;
      } else {
        (void)strtoll(begin, &number_end, 10);
        if (errno == ERANGE)
          ok = 0;
      }
      if (number_end != p)
        ok = 0;
    } else if (end - p >= 4 && (!memcmp(p, "null", 4) || !memcmp(p, "true", 4)))
      p += 4;
    else if (end - p >= 5 && !memcmp(p, "false", 5))
      p += 5;
    else if (*p == ':' || *p == ' ' || *p == '\t' || *p == '\r' || *p == '\n')
      p++;
    else
      ok = 0;
  }
  while (depth)
    if (frames[--depth].keys)
      json_object_put(frames[depth].keys);
  if (key_tok)
    json_tokener_free(key_tok);
  return ok;
}
/* Validate RFC 3629 before normalizing literal Unicode for json-c. */
static int json_utf8_valid(const unsigned char *text, size_t length) {
  for (size_t i = 0; i < length;) {
    unsigned char lead = text[i++];
    if (lead < 0x80) continue;
    size_t remaining;
    unsigned char first_min = 0x80, first_max = 0xbf;
    if (lead >= 0xc2 && lead <= 0xdf) remaining = 1;
    else if (lead >= 0xe0 && lead <= 0xef) {
      remaining = 2;
      if (lead == 0xe0) first_min = 0xa0;
      if (lead == 0xed) first_max = 0x9f;
    } else if (lead >= 0xf0 && lead <= 0xf4) {
      remaining = 3;
      if (lead == 0xf0) first_min = 0x90;
      if (lead == 0xf4) first_max = 0x8f;
    } else return 0;
    if (remaining > length - i || text[i] < first_min || text[i] > first_max) return 0;
    for (size_t j = 1; j < remaining; j++) if (text[i+j] < 0x80 || text[i+j] > 0xbf) return 0;
    i += remaining;
  }
  return 1;
}

/* json-c 0.18 strict mode on Alpine rejects literal non-ASCII strings.
 * Feed equivalent escapes to the strict parser; retain original lexical checks. */
static char *json_ascii(const unsigned char *text, size_t length, size_t *size) {
  if (length > (SIZE_MAX - 1) / 3) return NULL;
  char *ascii = malloc(length * 3 + 1);
  if (!ascii) return NULL;
  char *out = ascii;
  for (size_t i = 0; i < length;) {
    unsigned byte = text[i++];
    if (byte < 0x80) { *out++ = (char)byte; continue; }
    unsigned codepoint = byte & (byte < 0xe0 ? 0x1f : byte < 0xf0 ? 0x0f : 0x07);
    unsigned count = byte < 0xe0 ? 1 : byte < 0xf0 ? 2 : 3;
    while (count--) codepoint = (codepoint << 6) | (text[i++] & 0x3f);
    if (codepoint > 0xffff) {
      codepoint -= 0x10000;
      out += snprintf(out, 7, "\\u%04x", 0xd800 + (codepoint >> 10));
      codepoint = 0xdc00 + (codepoint & 0x3ff);
    }
    out += snprintf(out, 7, "\\u%04x", codepoint);
  }
  *out = 0;
  *size = (size_t)(out - ascii);
  return ascii;
}

int64_t fw_parse(const char *text) {
  if (!text)
    return 0;
  size_t n = strnlen(text, FETCH_MAX + 1);
  if (n > FETCH_MAX || !json_utf8_valid((const unsigned char *)text, n))
    return 0;
  size_t parsed_size = n;
  char *ascii = NULL;
  for (size_t i = 0; i < n; i++)
    if ((unsigned char)text[i] >= 0x80) {
      ascii = json_ascii((const unsigned char *)text, n, &parsed_size);
      if (!ascii) return 0;
      break;
    }
  const char *parsed = ascii ? ascii : text;
  struct json_tokener *tok = json_tokener_new_ex(32);
  if (!tok) { free(ascii); return 0; }
  json_tokener_set_flags(tok, JSON_TOKENER_STRICT | JSON_TOKENER_VALIDATE_UTF8);
  struct json_object *v = json_tokener_parse_ex(tok, parsed, (int)parsed_size + 1);
  size_t end = json_tokener_get_parse_end(tok);
  while (end < parsed_size && isspace((unsigned char)parsed[end]))
    end++;
  int ok = json_tokener_get_error(tok) == json_tokener_success && end == parsed_size;
  json_tokener_free(tok);
  free(ascii);
  if (ok)
    ok = json_unambiguous(text, n);
  if (!ok) {
    if (v)
      json_object_put(v);
    return 0;
  }
  return H(track(v, 1));
}
int64_t fw_kind(int64_t h) {
  if (!h)
    return 0;
  switch (json_object_get_type(P(struct json_object, h))) {
  case json_type_null:
    return 0;
  case json_type_boolean:
    return 1;
  case json_type_int:
    return 2;
  case json_type_string:
    return 3;
  case json_type_object:
    return 4;
  case json_type_array:
    return 5;
  case json_type_double:
    return 6;
  }
  return 0;
}
int64_t fw_get(int64_t h, const char *key) {
  struct json_object *v = NULL;
  if (fw_kind(h) != 4 || !key)
    return 0;
  json_object_object_get_ex(P(struct json_object, h), key, &v);
  return H(v);
}
int64_t fw_at(int64_t h, int64_t i) {
  return fw_kind(h) == 5 && i >= 0 &&
                 (uint64_t)i <
                     json_object_array_length(P(struct json_object, h))
             ? H(json_object_array_get_idx(P(struct json_object, h), i))
             : 0;
}
int64_t fw_count(int64_t h) {
  return fw_kind(h) == 5
             ? (int64_t)json_object_array_length(P(struct json_object, h))
         : fw_kind(h) == 4 ? json_object_object_length(P(struct json_object, h))
                           : 0;
}
const char *fw_text(int64_t h) {
  return fw_kind(h) == 3 ? json_object_get_string(P(struct json_object, h))
                         : "";
}
int64_t fw_integer(int64_t h) {
  return fw_kind(h) == 2 ? json_object_get_int64(P(struct json_object, h)) : 0;
}
int64_t fw_boolean(int64_t h) {
  return fw_kind(h) == 1 ? json_object_get_boolean(P(struct json_object, h))
                         : 0;
}
const char *fw_dump(int64_t h) {
  return h ? json_object_to_json_string_ext(P(struct json_object, h),
                                            JSON_C_TO_STRING_PLAIN)
           : "null";
}
int64_t fw_object(void) { return H(track(json_object_new_object(), 1)); }
int64_t fw_array(void) { return H(track(json_object_new_array(), 1)); }
int64_t fw_string(const char *v) {
  return H(track(json_object_new_string(v ? v : ""), 1));
}
int64_t fw_number(int64_t v) { return H(track(json_object_new_int64(v), 1)); }
int64_t fw_bool(int64_t v) {
  return H(track(json_object_new_boolean(v != 0), 1));
}
int64_t fw_set(int64_t h, const char *key, int64_t v) {
  if (fw_kind(h) != 4 || !key)
    return 0;
  return json_object_object_add(P(struct json_object, h), key,
                                json_object_get(P(struct json_object, v))) == 0;
}
int64_t fw_push(int64_t h, int64_t v) {
  return fw_kind(h) == 5 &&
         json_object_array_add(P(struct json_object, h),
                               json_object_get(P(struct json_object, v))) == 0;
}
int64_t fw_keys(int64_t h) {
  int64_t a = fw_array();
  if (fw_kind(h) == 4) {
    json_object_object_foreach(P(struct json_object, h), key, value) {
      (void)value;
      fw_push(a, fw_string(key));
    }
  }
  return a;
}
const char *fw_trim(const char *s) {
  if (!s)
    return "";
  while (isspace((unsigned char)*s))
    s++;
  size_t n = strlen(s);
  while (n && isspace((unsigned char)s[n - 1]))
    n--;
  return track(strndup(s, n), 0);
}
int64_t fw_chars(const char *s) {
  int64_t n = 0;
  if (s)
    while (*s) {
      if (((unsigned char)*s & 0xc0) != 0x80)
        n++;
      s++;
    }
  return n;
}
const char *fw_lower(const char *s) {
  char *v = (char *)copy(s);
  if (v)
    for (char *p = v; *p; p++)
      *p = (char)tolower((unsigned char)*p);
  return v ? v : "";
}
int64_t fw_equal(const char *a, const char *b) {
  return a && b && strcmp(a, b) == 0;
}
int64_t fw_starts(const char *s, const char *prefix) {
  return s && prefix && strncmp(s, prefix, strlen(prefix)) == 0;
}
const char *fw_part(const char *s, int64_t index) {
  if (!s || index < 0)
    return "";
  while (*s == '/')
    s++;
  for (int64_t i = 0; i < index; i++) {
    s = strchr(s, '/');
    if (!s)
      return "";
    s++;
  }
  const char *end = strchr(s, '/');
  return track(strndup(s, end ? (size_t)(end - s) : strlen(s)), 0);
}
static int private_ip(const char *s) {
  struct in_addr a;
  struct in6_addr b;
  if (inet_pton(AF_INET, s, &a) == 1) {
    uint32_t v = ntohl(a.s_addr);
    return (v >> 24) == 127 || (v >> 24) == 10 || (v >> 24) == 0 ||
           (v >> 16) == 0xa9fe || (v >> 20) == 0xac1 || (v >> 16) == 0xc0a8 ||
           (v >> 28) >= 14;
  }
  if (inet_pton(AF_INET6, s, &b) == 1) {
    if (IN6_IS_ADDR_V4MAPPED(&b)) {
      char mapped[INET_ADDRSTRLEN];
      inet_ntop(AF_INET, &b.s6_addr[12], mapped, sizeof(mapped));
      return private_ip(mapped);
    }
    return IN6_IS_ADDR_LOOPBACK(&b) || IN6_IS_ADDR_UNSPECIFIED(&b) ||
           (b.s6_addr[0] & 0xfe) == 0xfc ||
           (b.s6_addr[0] == 0xfe && (b.s6_addr[1] & 0xc0) == 0x80) ||
           b.s6_addr[0] == 0xff;
  }
  return 1;
}
int64_t fw_valid(const char *s, const char *kind) {
  if (!s || !kind)
    return 0;
  size_t n = strlen(s);
  if (!strcmp(kind, "uuid")) {
    if (n != 36)
      return 0;
    for (size_t i = 0; i < n; i++)
      if ((i == 8 || i == 13 || i == 18 || i == 23)
              ? s[i] != '-'
              : !isxdigit((unsigned char)s[i]))
        return 0;
    return 1;
  }
  if (!strcmp(kind, "id")) {
    if (!n || n > 19)
      return 0;
    for (size_t i = 0; i < n; i++)
      if (!isdigit((unsigned char)s[i]))
        return 0;
    errno = 0;
    long long v = strtoll(s, NULL, 10);
    return !errno && v > 0;
  }
  if (!strcmp(kind, "login")) {
    if (!n || n > 39)
      return 0;
    for (size_t i = 0; i < n; i++)
      if (!((s[i] >= 'a' && s[i] <= 'z') || (s[i] >= 'A' && s[i] <= 'Z') ||
            (s[i] >= '0' && s[i] <= '9') || s[i] == '-'))
        return 0;
    return 1;
  }
  if (!strcmp(kind, "github_part")) {
    if (!n || n > 100 || s[0] == '.')
      return 0;
    for (size_t i = 0; i < n; i++)
      if (!(isalnum((unsigned char)s[i]) || s[i] == '-' || s[i] == '_' ||
            s[i] == '.'))
        return 0;
    return 1;
  }
  if (!strcmp(kind, "email")) {
    const char *at = strchr(s, '@');
    if (!at || at == s || !at[1] || strchr(at + 1, '@') || !strchr(at + 1, '.'))
      return 0;
    for (size_t i = 0; i < n; i++)
      if (isspace((unsigned char)s[i]) || iscntrl((unsigned char)s[i]))
        return 0;
    return 1;
  }
  if (!strcmp(kind, "url")) {
    CURLU *u = curl_url();
    if (!u)
      return 0;
    int ok = curl_url_set(u, CURLUPART_URL, s, 0) == CURLUE_OK;
    char *scheme = NULL, *host = NULL;
    if (ok)
      ok = curl_url_get(u, CURLUPART_SCHEME, &scheme, 0) == CURLUE_OK &&
           curl_url_get(u, CURLUPART_HOST, &host, 0) == CURLUE_OK &&
           (!strcasecmp(scheme, "http") || !strcasecmp(scheme, "https")) &&
           *host;
    curl_free(scheme);
    curl_free(host);
    curl_url_cleanup(u);
    return ok;
  }
  if (!strcmp(kind, "return_path")) {
    if (!n || s[0] != '/' || s[1] == '/')
      return 0;
    for (size_t i = 0; i < n; i++)
      if (!((s[i] >= 'a' && s[i] <= 'z') || (s[i] >= 'A' && s[i] <= 'Z') ||
            isdigit((unsigned char)s[i]) || strchr("/-_.~", s[i])))
        return 0;
    return 1;
  }
  if (!strcmp(kind, "ip") || !strcmp(kind, "public_ip")) {
    struct in_addr a;
    struct in6_addr b;
    int ok = inet_pton(AF_INET, s, &a) == 1 || inet_pton(AF_INET6, s, &b) == 1;
    return ok && (strcmp(kind, "public_ip") || !private_ip(s));
  }
  if (!strcmp(kind, "filename")) {
    if (!n || n > 100 || s[0] == '.')
      return 0;
    for (size_t i = 0; i < n; i++)
      if (!(isalnum((unsigned char)s[i]) || s[i] == '-' || s[i] == '.'))
        return 0;
    return 1;
  }
  return 0;
}
const char *fw_uuid(void) {
  unsigned char b[16];
  if (RAND_bytes(b, 16) != 1)
    return "";
  b[6] = (b[6] & 15) | 64;
  b[8] = (b[8] & 63) | 128;
  char s[37];
  snprintf(
      s, sizeof(s),
      "%02x%02x%02x%02x-%02x%02x-%02x%02x-%02x%02x-%02x%02x%02x%02x%02x%02x",
      b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7], b[8], b[9], b[10], b[11],
      b[12], b[13], b[14], b[15]);
  return copy(s);
}
int64_t fw_now(void) { return time(NULL); }
#define RATE_CAPACITY 4096u
#define RATE_BUCKETS 8192u
typedef struct {
  char key[256];
  time_t start;
  int64_t count;
  unsigned next;
} Rate;
static Rate rates[RATE_CAPACITY];
static unsigned rate_buckets[RATE_BUCKETS];
static unsigned rate_used;
static pthread_mutex_t rate_mutex = PTHREAD_MUTEX_INITIALIZER;
static unsigned rate_bucket(const char *key) {
  uint64_t hash = UINT64_C(14695981039346656037);
  for (const unsigned char *p = (const unsigned char *)key; *p; p++)
    hash = (hash ^ *p) * UINT64_C(1099511628211);
  return (unsigned)(hash & (RATE_BUCKETS - 1));
}
int64_t fw_rate(const char *key, int64_t max, int64_t seconds) {
  if (!key || strlen(key) >= sizeof(rates[0].key) || max < 1 || seconds < 1)
    return 0;
  time_t now = time(NULL);
  unsigned bucket = rate_bucket(key);
  pthread_mutex_lock(&rate_mutex);
  unsigned link = rate_buckets[bucket];
  while (link && strcmp(rates[link - 1].key, key))
    link = rates[link - 1].next;
  unsigned slot;
  if (link)
    slot = link - 1;
  else {
    if (rate_used < RATE_CAPACITY)
      slot = rate_used++;
    else {
      /* Preserve bounded storage and the previous oldest-entry eviction rule:
       * entries started in this same second cannot be evicted. */
      slot = RATE_CAPACITY;
      time_t oldest = now;
      for (unsigned i = 0; i < RATE_CAPACITY; i++) {
        if (rates[i].start < oldest) {
          oldest = rates[i].start;
          slot = i;
        }
      }
      if (slot == RATE_CAPACITY) {
        pthread_mutex_unlock(&rate_mutex);
        return 0;
      }
      unsigned *previous = &rate_buckets[rate_bucket(rates[slot].key)];
      while (*previous != slot + 1)
        previous = &rates[*previous - 1].next;
      *previous = rates[slot].next;
    }
    Rate *r = &rates[slot];
    snprintf(r->key, sizeof(r->key), "%s", key);
    r->start = now;
    r->count = 0;
    r->next = rate_buckets[bucket];
    rate_buckets[bucket] = slot + 1;
  }
  Rate *r = &rates[slot];
  if (now - r->start >= seconds) {
    r->start = now;
    r->count = 0;
  }
  int ok = r->count < max;
  if (ok)
    r->count++;
  pthread_mutex_unlock(&rate_mutex);
  return ok;
}
const char *fw_urlencode(const char *s) {
  pthread_once(&curl_once, init_curl);
  if (!curl_ready)
    return "";
  char *e = curl_easy_escape(NULL, s ? s : "", 0);
  const char *out = copy(e);
  curl_free(e);
  return out ? out : "";
}
/* Capacity includes the terminating NUL. Each growth is geometric and capped
 * at the externally visible payload limit plus one. */
static int reserve_buffer(char **data, size_t *capacity, size_t needed,
                          size_t limit) {
  if (needed > limit + 1)
    return 0;
  if (needed <= *capacity)
    return 1;
  size_t next = *capacity ? *capacity : 4096;
  if (next > limit + 1)
    next = limit + 1;
  while (next < needed) {
    if (next > (limit + 1) / 2) {
      next = limit + 1;
      break;
    }
    next *= 2;
  }
  char *p = realloc(*data, next);
  if (!p)
    return 0;
  *data = p;
  *capacity = next;
  return 1;
}
typedef struct {
  char *data;
  size_t size, capacity;
} Buffer;
static size_t receive_http(char *data, size_t size, size_t count, void *cls) {
  Buffer *b = cls;
  if (size && count > SIZE_MAX / size)
    return 0;
  size_t n = size * count;
  if (n > FETCH_MAX - b->size)
    return 0;
  if (!reserve_buffer(&b->data, &b->capacity, b->size + n + 1, FETCH_MAX))
    return 0;
  char *p = b->data;
  memcpy(p + b->size, data, n);
  b->size += n;
  p[b->size] = 0;
  return n;
}
static int append_header(struct curl_slist **headers, const char *value) {
  struct curl_slist *next = curl_slist_append(*headers, value);
  if (!next)
    return 0;
  *headers = next;
  return 1;
}
static int64_t fetch_response(const char *url, const char *method,
                              const char *body, const char *bearer, int json) {
  if (!url || strnlen(url, 8193) > 8192)
    return 0;
  size_t bearer_size = bearer ? strnlen(bearer, 16385) : 0;
  if (bearer_size > 16384)
    return 0;
  for (size_t i = 0; i < bearer_size; i++)
    if ((unsigned char)bearer[i] <= 32 || (unsigned char)bearer[i] >= 127)
      return 0;
  CURL *c = get_curl();
  if (!c)
    return 0;
  Buffer b = {0};
  struct curl_slist *headers = NULL;
  if (!append_header(&headers, "Accept: application/json"))
    return 0;
  if (bearer_size) {
    char *h = malloc(bearer_size + 23);
    if (!h) {
      curl_slist_free_all(headers);
      return 0;
    }
    snprintf(h, bearer_size + 23, "Authorization: Bearer %s", bearer);
    int ok = append_header(&headers, h);
    free(h);
    if (!ok) {
      curl_slist_free_all(headers);
      return 0;
    }
  }
  if (json && !append_header(&headers, "Content-Type: application/json")) {
    curl_slist_free_all(headers);
    return 0;
  }
  curl_easy_setopt(c, CURLOPT_URL, url);
#if LIBCURL_VERSION_NUM >= 0x075500
  curl_easy_setopt(c, CURLOPT_PROTOCOLS_STR, "http,https");
  curl_easy_setopt(c, CURLOPT_REDIR_PROTOCOLS_STR, "http,https");
#else
  curl_easy_setopt(c, CURLOPT_PROTOCOLS, CURLPROTO_HTTP | CURLPROTO_HTTPS);
  curl_easy_setopt(c, CURLOPT_REDIR_PROTOCOLS,
                   CURLPROTO_HTTP | CURLPROTO_HTTPS);
#endif
  curl_easy_setopt(c, CURLOPT_FOLLOWLOCATION, 0L);
  curl_easy_setopt(c, CURLOPT_CONNECTTIMEOUT, 3L);
  curl_easy_setopt(c, CURLOPT_TIMEOUT, 10L);
  curl_easy_setopt(c, CURLOPT_NOSIGNAL, 1L);
  curl_easy_setopt(c, CURLOPT_USERAGENT, "portfolio-forge/0.1");
  curl_easy_setopt(c, CURLOPT_HTTPHEADER, headers);
  curl_easy_setopt(c, CURLOPT_WRITEFUNCTION, receive_http);
  curl_easy_setopt(c, CURLOPT_WRITEDATA, &b);
  if (method && (!strcmp(method, "POST") || !strcmp(method, "PUT") ||
                 !strcmp(method, "DELETE"))) {
    curl_easy_setopt(c, CURLOPT_CUSTOMREQUEST, method);
    curl_easy_setopt(c, CURLOPT_POST, 1L);
    curl_easy_setopt(c, CURLOPT_POSTFIELDS, body ? body : "");
  }
  CURLcode rc = curl_easy_perform(c);
  long status = 0;
  curl_easy_getinfo(c, CURLINFO_RESPONSE_CODE, &status);
  int64_t out = fw_object();
  fw_set(out, "status", fw_number(rc == CURLE_OK ? status : 0));
  fw_set(out, "data",
         b.data && !memchr(b.data, 0, b.size) ? fw_parse(b.data) : 0);
  curl_easy_reset(c);
  free(b.data);
  curl_slist_free_all(headers);
  return out;
}
int64_t fw_fetch(const char *url, const char *method, const char *body,
                 const char *bearer) {
  int64_t response = fetch_response(url, method, body, bearer, 0);
  int64_t status = fw_integer(fw_get(response, "status"));
  return status >= 200 && status < 300 ? fw_get(response, "data") : 0;
}
int64_t fw_request(const char *url, const char *method, const char *body,
                   const char *bearer) {
  if (!method || (strcmp(method, "GET") && strcmp(method, "POST") &&
                  strcmp(method, "PUT") && strcmp(method, "DELETE")))
    return 0;
  return fetch_response(url, method, body, bearer, 1);
}
static char *b64(const unsigned char *data, size_t n) {
  char *s = track(malloc(4 * ((n + 2) / 3) + 1), 0);
  if (!s)
    return NULL;
  int len = EVP_EncodeBlock((unsigned char *)s, data, (int)n);
  while (len && s[len - 1] == '=')
    len--;
  s[len] = 0;
  for (int i = 0; i < len; i++) {
    if (s[i] == '+')
      s[i] = '-';
    else if (s[i] == '/')
      s[i] = '_';
  }
  return s;
}
static unsigned char *unb64(const char *s, size_t n, size_t *out) {
  if (!n || n > 65536 || n % 4 == 1)
    return NULL;
  const char *alphabet =
      "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";
  const char *last = strchr(alphabet, s[n - 1]);
  if (!last || (n % 4 == 2 && ((last - alphabet) & 15)) ||
      (n % 4 == 3 && ((last - alphabet) & 3)))
    return NULL;
  size_t full = ((n + 3) / 4) * 4;
  char *tmp = malloc(full + 1);
  unsigned char *data = track(malloc(full + 1), 0);
  if (!tmp || !data) {
    free(tmp);
    return NULL;
  }
  for (size_t i = 0; i < n; i++) {
    unsigned char ch = s[i];
    if (!(isalnum(ch) || ch == '-' || ch == '_')) {
      free(tmp);
      return NULL;
    }
    tmp[i] = ch == '-' ? '+' : ch == '_' ? '/' : ch;
  }
  for (size_t i = n; i < full; i++)
    tmp[i] = '=';
  tmp[full] = 0;
  int len = EVP_DecodeBlock(data, (unsigned char *)tmp, (int)full);
  free(tmp);
  if (len < 0)
    return NULL;
  *out = (size_t)len - (full - n);
  data[*out] = 0;
  return data;
}
const char *fw_jwt_sign(int64_t claims, const char *secret) {
  if (fw_kind(claims) != 4 || !secret || !*secret)
    return "";
  const char *payload = fw_dump(claims);
  if (strnlen(secret, 65537) > 65536 || strlen(payload) > 12000)
    return "";
  char *p = b64((unsigned char *)payload, strlen(payload));
  if (!p)
    return "";
  size_t n = strlen(p) + 38;
  char *message = track(malloc(n), 0);
  if (!message)
    return "";
  snprintf(message, n, "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.%s", p);
  unsigned char mac[EVP_MAX_MD_SIZE];
  unsigned int len = 0;
  if (!HMAC(EVP_sha256(), secret, (int)strlen(secret), (unsigned char *)message,
            strlen(message), mac, &len))
    return "";
  char *sig = b64(mac, len);
  if (!sig)
    return "";
  size_t total = strlen(message) + strlen(sig) + 2;
  char *token = track(malloc(total), 0);
  if (!token)
    return "";
  snprintf(token, total, "%s.%s", message, sig);
  return token;
}
int64_t fw_jwt_verify(const char *token, const char *secret) {
  if (!token || !secret || !*secret || strnlen(token, 16385) > 16384 ||
      strnlen(secret, 65537) > 65536)
    return 0;
  const char *a = strchr(token, '.');
  if (!a)
    return 0;
  const char *b = strchr(a + 1, '.');
  if (!b || strlen(b + 1) != 43 || strchr(b + 1, '.'))
    return 0;
  size_t sn;
  unsigned char *sig = unb64(b + 1, 43, &sn);
  if (!sig || sn != 32)
    return 0;
  /* Authenticate the bounded encoded content before spending work on attacker
   * supplied JSON. The configured algorithm is always HS256, never header-led.
   */
  unsigned char mac[EVP_MAX_MD_SIZE];
  unsigned int len = 0;
  if (!HMAC(EVP_sha256(), secret, (int)strlen(secret), (unsigned char *)token,
            b - token, mac, &len) ||
      len != sn || CRYPTO_memcmp(mac, sig, sn))
    return 0;
  size_t hn, pn;
  unsigned char *header = unb64(token, a - token, &hn),
                *payload = unb64(a + 1, b - a - 1, &pn);
  if (!header || !payload || strlen((char *)header) != hn ||
      strlen((char *)payload) != pn)
    return 0;
  int64_t h = fw_parse((char *)header);
  if (fw_kind(h) != 4 || strcmp(fw_text(fw_get(h, "alg")), "HS256") ||
      fw_has(h, "crit") || fw_has(h, "b64"))
    return 0;
  int64_t claims = fw_parse((char *)payload);
  if (fw_kind(claims) != 4 || fw_kind(fw_get(claims, "exp")) != 2 ||
      fw_integer(fw_get(claims, "exp")) <= fw_now() ||
      fw_kind(fw_get(claims, "sub")) != 3 || !*fw_text(fw_get(claims, "sub")) ||
      fw_kind(fw_get(claims, "role")) != 3 ||
      (fw_has(claims, "nbf") && (fw_kind(fw_get(claims, "nbf")) != 2 ||
                                 fw_integer(fw_get(claims, "nbf")) > fw_now())))
    return 0;
  return claims;
}
const char *fw_read(const char *path) {
  FILE *f = fopen(path, "rb");
  if (!f)
    return "";
  if (fseek(f, 0, SEEK_END)) {
    fclose(f);
    return "";
  }
  long size = ftell(f);
  if (size < 0 || size > FETCH_MAX) {
    fclose(f);
    return "";
  }
  rewind(f);
  char *data = track(malloc((size_t)size + 1), 0);
  if (!data) {
    fclose(f);
    return "";
  }
  size_t n = fread(data, 1, size, f);
  fclose(f);
  data[n] = 0;
  return data;
}

typedef struct {
  struct MHD_Connection *connection;
  char *method, *path, *body;
  size_t size, capacity;
  struct MHD_Response *response;
  unsigned status;
  char *origin;
  struct MHD_PostProcessor *post;
  int error, fd, files, finalized;
  size_t file_size;
  char temp[512], extension[8];
  char ip[INET6_ADDRSTRLEN];
  int ip_ready, parts_ready;
  int64_t path_count;
  char *part_storage;
  const char *parts[8];
  char storage[];
} Request;
/* Own method, path and a lazy segment scratch buffer in the same allocation
 * as the request. None of these pointers borrow MHD callback storage. */
static Request *new_request(struct MHD_Connection *connection, const char *path,
                            const char *method) {
  size_t path_size = strlen(path) + 1, method_size = strlen(method) + 1;
  if (method_size > SIZE_MAX - sizeof(Request) ||
      path_size > (SIZE_MAX - sizeof(Request) - method_size) / 2)
    return NULL;
  Request *r = calloc(1, sizeof(*r) + method_size + 2 * path_size);
  if (!r)
    return NULL;
  r->fd = -1;
  r->connection = connection;
  r->method = r->storage;
  r->path = r->method + method_size;
  r->part_storage = r->path + path_size;
  r->path_count = -1;
  memcpy(r->method, method, method_size);
  memcpy(r->path, path, path_size);
  return r;
}
#define PROXY_MAX 64u
typedef struct {
  unsigned char bytes[16];
  int family;
  unsigned prefix;
} ProxyNetwork;
static ProxyNetwork trusted_proxies[PROXY_MAX];
static size_t trusted_proxy_count;
static int parse_proxy_network(const char *text, ProxyNetwork *out) {
  char address[INET6_ADDRSTRLEN + 5];
  size_t length = strlen(text);
  if (!length || length >= sizeof(address))
    return 0;
  memcpy(address, text, length + 1);
  char *slash = strchr(address, '/');
  unsigned prefix = 0;
  if (slash) {
    *slash++ = 0;
    if (!*slash)
      return 0;
    for (const char *p = slash; *p; p++) {
      if (!isdigit((unsigned char)*p))
        return 0;
      prefix = prefix * 10 + (unsigned)(*p - '0');
      if (prefix > 128)
        return 0;
    }
  }
  if (inet_pton(AF_INET, address, out->bytes) == 1) {
    out->family = AF_INET;
    out->prefix = slash ? prefix : 32;
    return out->prefix <= 32;
  }
  if (inet_pton(AF_INET6, address, out->bytes) == 1) {
    out->family = AF_INET6;
    out->prefix = slash ? prefix : 128;
    return out->prefix <= 128;
  }
  return 0;
}
static int configure_proxies(const char *config) {
  trusted_proxy_count = 0;
  ProxyNetwork parsed[PROXY_MAX];
  size_t count = 0;
  if (!config || !*config)
    return 1;
  const char *cursor = config;
  while (*cursor) {
    while (isspace((unsigned char)*cursor))
      cursor++;
    const char *end = strchr(cursor, ',');
    if (!end)
      end = cursor + strlen(cursor);
    const char *trimmed = end;
    while (trimmed > cursor && isspace((unsigned char)trimmed[-1]))
      trimmed--;
    size_t length = (size_t)(trimmed - cursor);
    char token[INET6_ADDRSTRLEN + 5];
    if (!length || length >= sizeof(token) || count == PROXY_MAX)
      return 0;
    memcpy(token, cursor, length);
    token[length] = 0;
    if (!parse_proxy_network(token, &parsed[count]))
      return 0;
    count++;
    if (!*end) {
      memcpy(trusted_proxies, parsed, count * sizeof(parsed[0]));
      trusted_proxy_count = count;
      return 1;
    }
    cursor = end + 1;
    if (!*cursor)
      return 0;
  }
  return 1;
}
static int proxy_matches(const ProxyNetwork *network, int family,
                         const unsigned char *bytes) {
  if (network->family != family)
    return 0;
  unsigned whole = network->prefix / 8, rest = network->prefix % 8;
  if (memcmp(network->bytes, bytes, whole))
    return 0;
  return !rest ||
         !((network->bytes[whole] ^ bytes[whole]) & (0xffu << (8 - rest)));
}
static int trusted_peer(const struct sockaddr *peer) {
  const unsigned char *bytes;
  int family = peer->sa_family;
  if (family == AF_INET)
    bytes =
        (const unsigned char *)&((const struct sockaddr_in *)peer)->sin_addr;
  else if (family == AF_INET6)
    bytes =
        (const unsigned char *)&((const struct sockaddr_in6 *)peer)->sin6_addr;
  else
    return 0;
  for (size_t i = 0; i < trusted_proxy_count; i++)
    if (proxy_matches(&trusted_proxies[i], family, bytes))
      return 1;
  return 0;
}
static fw_handler app_handler;
static volatile sig_atomic_t stopping;
const char *fw_method(int64_t h) { return h ? P(Request, h)->method : ""; }
const char *fw_path(int64_t h) { return h ? P(Request, h)->path : ""; }
const char *fw_header(int64_t h, const char *name) {
  const char *s = h ? MHD_lookup_connection_value(P(Request, h)->connection,
                                                  MHD_HEADER_KIND, name)
                    : NULL;
  return s ? s : "";
}
const char *fw_query(int64_t h, const char *name) {
  const char *s = h ? MHD_lookup_connection_value(P(Request, h)->connection,
                                                  MHD_GET_ARGUMENT_KIND, name)
                    : NULL;
  return s ? s : "";
}
const char *fw_body(int64_t h) {
  return h && P(Request, h)->body ? P(Request, h)->body : "";
}
const char *fw_ip(int64_t h) {
  if (!h)
    return "";
  Request *r = P(Request, h);
  if (r->ip_ready)
    return r->ip;
  r->ip_ready = 1;
  const union MHD_ConnectionInfo *info = MHD_get_connection_info(
      r->connection, MHD_CONNECTION_INFO_CLIENT_ADDRESS);
  if (!info || !info->client_addr)
    return r->ip;
  struct sockaddr *addr = info->client_addr;
  if (addr->sa_family == AF_INET)
    inet_ntop(AF_INET, &((struct sockaddr_in *)addr)->sin_addr, r->ip,
              sizeof(r->ip));
  else if (addr->sa_family == AF_INET6)
    inet_ntop(AF_INET6, &((struct sockaddr_in6 *)addr)->sin6_addr, r->ip,
              sizeof(r->ip));
  else
    return r->ip;
  const char *proxy = fw_header(h, "X-Real-IP");
  if (*proxy && trusted_peer(addr) && fw_valid(proxy, "ip")) {
    struct in_addr a;
    struct in6_addr b;
    if (inet_pton(AF_INET, proxy, &a) == 1)
      inet_ntop(AF_INET, &a, r->ip, sizeof(r->ip));
    else {
      inet_pton(AF_INET6, proxy, &b);
      inet_ntop(AF_INET6, &b, r->ip, sizeof(r->ip));
    }
  }
  return r->ip;
}
const char *fw_segment(int64_t h, int64_t i) {
  if (!h || i < 0)
    return "";
  Request *r = P(Request, h);
  if ((uint64_t)i >= sizeof(r->parts) / sizeof(r->parts[0]))
    return fw_part(r->path, i);
  if (!r->parts_ready) {
    memcpy(r->part_storage, r->path, strlen(r->path) + 1);
    char *part = r->part_storage;
    while (*part == '/')
      part++;
    for (size_t j = 0; j < sizeof(r->parts) / sizeof(r->parts[0]); j++) {
      r->parts[j] = part;
      char *slash = strchr(part, '/');
      if (!slash)
        break;
      *slash = 0;
      part = slash + 1;
    }
    r->parts_ready = 1;
  }
  return r->parts[i] ? r->parts[i] : "";
}
int64_t fw_segments(int64_t h) {
  if (!h)
    return 0;
  Request *r = P(Request, h);
  if (r->path_count >= 0)
    return r->path_count;
  const char *s = r->path;
  if (*s == '/')
    s++;
  int64_t n = *s ? 1 : 0;
  while (*s)
    if (*s++ == '/')
      n++;
  r->path_count = n;
  return n;
}
static int64_t response(Request *r, unsigned status, const char *body,
                        const char *type) {
  if (!r)
    return 0;
  if (r->response)
    MHD_destroy_response(r->response);
  r->response = MHD_create_response_from_buffer(body ? strlen(body) : 0,
                                                (void *)(body ? body : ""),
                                                MHD_RESPMEM_MUST_COPY);
  if (!r->response)
    return 0;
  r->status = status;
  MHD_add_response_header(r->response, "Content-Type", type);
  MHD_add_response_header(r->response, "X-Content-Type-Options", "nosniff");
  return 1;
}
int64_t fw_respond(int64_t h, int64_t status, const char *body) {
  return response(P(Request, h), (unsigned)status, body,
                  "application/json; charset=utf-8");
}
int64_t fw_content_type(int64_t h, const char *value) {
  Request *r = P(Request, h);
  if (!r || !r->response)
    return 0;
  MHD_del_response_header(r->response, "Content-Type",
                          "application/json; charset=utf-8");
  return MHD_add_response_header(r->response, "Content-Type", value) == MHD_YES;
}
int64_t fw_redirect(int64_t h, const char *url) {
  if (!h || !url || strchr(url, '\r') || strchr(url, '\n'))
    return 0;
  if (!response(P(Request, h), 302, "", "text/plain"))
    return 0;
  MHD_add_response_header(P(Request, h)->response, "Location", url);
  MHD_add_response_header(P(Request, h)->response, "Cache-Control", "no-store");
  return 1;
}
int64_t fw_cors(int64_t h, const char *allowed) {
  Request *r = P(Request, h);
  if (!r)
    return 0;
  const char *origin = fw_header(h, "Origin");
  if (!*origin || !allowed)
    return 0;
  const char *s = allowed;
  while (*s) {
    const char *e = strchr(s, ',');
    size_t n = e ? (size_t)(e - s) : strlen(s);
    while (n && isspace((unsigned char)*s)) {
      s++;
      n--;
    }
    while (n && isspace((unsigned char)s[n - 1]))
      n--;
    if (n == strlen(origin) && !strncmp(s, origin, n)) {
      free(r->origin);
      r->origin = strdup(origin);
      return 1;
    }
    if (!e)
      break;
    s = e + 1;
  }
  return 0;
}
static const char *mime(const char *name) {
  const char *ext = strrchr(name, '.');
  if (!ext)
    return "application/octet-stream";
  if (!strcasecmp(ext, ".png"))
    return "image/png";
  if (!strcasecmp(ext, ".jpg") || !strcasecmp(ext, ".jpeg"))
    return "image/jpeg";
  if (!strcasecmp(ext, ".gif"))
    return "image/gif";
  if (!strcasecmp(ext, ".webp"))
    return "image/webp";
  if (!strcasecmp(ext, ".svg"))
    return "image/svg+xml";
  if (!strcasecmp(ext, ".pdf"))
    return "application/pdf";
  return "application/octet-stream";
}
int64_t fw_file(int64_t h, const char *root, const char *name) {
  if (!h || !fw_valid(name, "filename"))
    return fw_respond(h, 404, "{\"error\":\"not_found\"}");
  int dir = open(root, O_RDONLY | O_DIRECTORY);
  if (dir < 0)
    return fw_respond(h, 404, "{\"error\":\"not_found\"}");
  int fd = openat(dir, name, O_RDONLY | O_NOFOLLOW);
  close(dir);
  struct stat st;
  if (fd < 0 || fstat(fd, &st) || !S_ISREG(st.st_mode)) {
    if (fd >= 0)
      close(fd);
    return fw_respond(h, 404, "{\"error\":\"not_found\"}");
  }
  Request *r = P(Request, h);
  if (r->response)
    MHD_destroy_response(r->response);
  r->response = MHD_create_response_from_fd64((uint64_t)st.st_size, fd);
  if (!r->response) {
    close(fd);
    return 0;
  }
  r->status = 200;
  MHD_add_response_header(r->response, "Content-Type", mime(name));
  MHD_add_response_header(r->response, "X-Content-Type-Options", "nosniff");
  MHD_add_response_header(
      r->response, "Content-Security-Policy",
      "default-src 'none'; style-src 'unsafe-inline'; sandbox");
  return 1;
}
static enum MHD_Result upload_part(void *cls, enum MHD_ValueKind kind,
                                   const char *key, const char *filename,
                                   const char *content_type,
                                   const char *encoding, const char *data,
                                   uint64_t off, size_t size) {
  Request *r = cls;
  (void)kind;
  (void)key;
  (void)content_type;
  (void)encoding;
  if (!filename || r->error)
    return MHD_NO;
  if (off == 0 && r->fd < 0) {
    const char *ext = strrchr(filename, '.');
    if (!ext || strlen(ext) > 7 ||
        !strcmp(mime(ext), "application/octet-stream")) {
      r->error = 400;
      return MHD_NO;
    }
    if (++r->files > 1) {
      r->error = 400;
      return MHD_NO;
    }
    snprintf(r->extension, sizeof(r->extension), "%s", ext);
    for (char *p = r->extension; *p; p++)
      *p = (char)tolower((unsigned char)*p);
    const char *root = fw_env("UPLOAD_DIR", "./uploads");
    if (mkdir(root, 0755) && errno != EEXIST) {
      r->error = 500;
      return MHD_NO;
    }
    if (snprintf(r->temp, sizeof(r->temp), "%s/.upload-XXXXXX", root) >=
        (int)sizeof(r->temp)) {
      r->error = 500;
      return MHD_NO;
    }
    r->fd = mkstemp(r->temp);
    if (r->fd < 0) {
      r->error = 500;
      return MHD_NO;
    }
  } else if (off == 0 && r->fd >= 0 && r->file_size) {
    r->error = 400;
    return MHD_NO;
  }
  if (off != r->file_size || size > FILE_MAX - r->file_size) {
    r->error = 413;
    return MHD_NO;
  }
  size_t written = 0;
  while (written < size) {
    ssize_t n = write(r->fd, data + written, size - written);
    if (n < 0 && errno == EINTR)
      continue;
    if (n <= 0) {
      r->error = 500;
      return MHD_NO;
    }
    written += (size_t)n;
  }
  r->file_size += size;
  return MHD_YES;
}
const char *fw_upload(int64_t h, const char *root) {
  Request *r = P(Request, h);
  if (!r || r->error || r->fd < 0 || r->files != 1 || !r->file_size ||
      r->finalized)
    return "";
  char destination[512], name[64];
  snprintf(name, sizeof(name), "%s%s", fw_uuid(), r->extension);
  if (!*name || snprintf(destination, sizeof(destination), "%s/%s", root,
                         name) >= (int)sizeof(destination))
    return "";
  if (fsync(r->fd) || fchmod(r->fd, 0644) || rename(r->temp, destination))
    return "";
  close(r->fd);
  r->fd = -1;
  r->finalized = 1;
  r->temp[0] = 0;
  return copy(name);
}
static void completed(void *cls, struct MHD_Connection *connection,
                      void **context, enum MHD_RequestTerminationCode code) {
  (void)cls;
  (void)connection;
  (void)code;
  Request *r = *context;
  if (!r)
    return;
  if (r->post)
    MHD_destroy_post_processor(r->post);
  if (r->fd >= 0)
    close(r->fd);
  if (*r->temp)
    unlink(r->temp);
  if (r->response)
    MHD_destroy_response(r->response);
  free(r->body);
  free(r->origin);
  free(r);
  *context = NULL;
}
static enum MHD_Result serve(void *cls, struct MHD_Connection *connection,
                             const char *path, const char *method,
                             const char *version, const char *data,
                             size_t *size, void **context) {
  (void)cls;
  (void)version;
  Request *r = *context;
  if (!r) {
    r = new_request(connection, path, method);
    if (!r)
      return MHD_NO;
    *context = r;
    const char *type = MHD_lookup_connection_value(connection, MHD_HEADER_KIND,
                                                   "Content-Type");
    if (type && !strncasecmp(type, "multipart/form-data", 19)) {
      r->post = MHD_create_post_processor(connection, 65536, upload_part, r);
      if (!r->post)
        r->error = 400;
    }
    return MHD_YES;
  }
  if (*size) {
    if (*size > BODY_MAX - r->size)
      r->error = 413;
    if (!r->post && memchr(data, 0, *size))
      r->error = 400;
    if (!r->error) {
      if (r->post) {
        if (MHD_post_process(r->post, data, *size) != MHD_YES && !r->error)
          r->error = 400;
      } else if (*size > JSON_MAX - r->size)
        r->error = 413;
      else {
        if (!reserve_buffer(&r->body, &r->capacity, r->size + *size + 1,
                            JSON_MAX))
          r->error = 500;
        else {
          char *buf = r->body;
          memcpy(buf + r->size, data, *size);
          buf[r->size + *size] = 0;
        }
      }
      r->size += *size;
    }
    *size = 0;
    return MHD_YES;
  }
  if (r->response)
    return MHD_YES;
  fw_scope_begin();
  if (r->error)
    fw_respond(
        H(r), r->error,
        r->error == 413
            ? "{\"error\":\"validation\",\"message\":\"payload too large\"}"
        : r->error == 400
            ? "{\"error\":\"validation\",\"message\":\"invalid upload\"}"
            : "{\"error\":\"internal\"}");
  else
    app_handler(H(r));
  if (!r->response)
    fw_respond(H(r), 500, "{\"error\":\"internal\"}");
  if (r->origin) {
    MHD_add_response_header(r->response, "Access-Control-Allow-Origin",
                            r->origin);
    MHD_add_response_header(r->response, "Vary", "Origin");
    MHD_add_response_header(r->response, "Access-Control-Allow-Methods",
                            "GET, POST, PUT, DELETE, OPTIONS");
    MHD_add_response_header(r->response, "Access-Control-Allow-Headers",
                            "authorization, content-type");
    MHD_add_response_header(r->response, "Access-Control-Max-Age", "3600");
  }
  enum MHD_Result result =
      MHD_queue_response(connection, r->status, r->response);
  fw_scope_end();
  return result;
}
static void stop_server(int sig) {
  (void)sig;
  stopping = 1;
}
/* Runtime feature checks keep the same binary usable when the MHD build or
 * platform lacks epoll. An explicit mode permits comparable deployment tests.
 */
static unsigned polling_flags(const char *mode, int epoll, int poll) {
  unsigned base = MHD_USE_INTERNAL_POLLING_THREAD | MHD_USE_ERROR_LOG;
  if (!mode || !*mode || !strcmp(mode, "auto")) {
    if (epoll)
      return base | MHD_USE_EPOLL;
    if (poll)
      return base | MHD_USE_POLL;
    return base;
  }
  if (!strcmp(mode, "epoll"))
    return base | (epoll ? MHD_USE_EPOLL : poll ? MHD_USE_POLL : 0);
  if (!strcmp(mode, "poll"))
    return base | (poll ? MHD_USE_POLL : 0);
  return !strcmp(mode, "select") ? base : 0;
}
static struct MHD_Daemon *start_daemon(unsigned flags, struct sockaddr_in *addr,
                                       unsigned workers, int connection_threads) {
  if (connection_threads)
    return MHD_start_daemon(
        flags, ntohs(addr->sin_port), NULL, NULL, serve, NULL,
        MHD_OPTION_SOCK_ADDR, addr, MHD_OPTION_CONNECTION_LIMIT, 256u,
        MHD_OPTION_CONNECTION_TIMEOUT, 30u,
        MHD_OPTION_CONNECTION_MEMORY_LIMIT, (size_t)128 * 1024,
        MHD_OPTION_NOTIFY_COMPLETED, completed, NULL, MHD_OPTION_END);
  return MHD_start_daemon(
      flags, ntohs(addr->sin_port), NULL, NULL, serve, NULL,
      MHD_OPTION_SOCK_ADDR, addr, MHD_OPTION_THREAD_POOL_SIZE, workers,
      MHD_OPTION_CONNECTION_LIMIT, 256u, MHD_OPTION_CONNECTION_TIMEOUT, 30u,
      MHD_OPTION_CONNECTION_MEMORY_LIMIT, (size_t)128 * 1024,
      MHD_OPTION_NOTIFY_COMPLETED, completed, NULL, MHD_OPTION_END);
}
int64_t fw_run(const char *host, int64_t port, int64_t workers,
               fw_handler handler) {
  if (!host || !handler || port < 1 || port > 65535 || workers < 1 ||
      workers > 64)
    return 1;
  struct sockaddr_in addr = {0};
  addr.sin_family = AF_INET;
  addr.sin_port = htons((uint16_t)port);
  if (inet_pton(AF_INET, host, &addr.sin_addr) != 1)
    return 1;
  if (!configure_proxies(fw_env("FORGE_TRUSTED_PROXIES", ""))) {
    fprintf(stderr, "Invalid FORGE_TRUSTED_PROXIES: use comma-separated "
                    "IPs/CIDRs (max 64)\n");
    return 1;
  }
  pthread_once(&curl_once, init_curl);
  if (!curl_ready)
    return 1;
  const char *threads = fw_env("FORGE_WEB_THREADS", "connection");
  int connection_threads = !strcmp(threads, "connection");
  if (!connection_threads && strcmp(threads, "pool")) {
    fprintf(stderr, "Invalid FORGE_WEB_THREADS: use connection or pool\n");
    return 1;
  }
  app_handler = handler;
  stopping = 0;
  signal(SIGTERM, stop_server);
  signal(SIGINT, stop_server);
  signal(SIGPIPE, SIG_IGN);
  unsigned flags =
      polling_flags(fw_env("FORGE_WEB_POLL", "auto"),
                    MHD_is_feature_supported(MHD_FEATURE_EPOLL) == MHD_YES,
                    MHD_is_feature_supported(MHD_FEATURE_POLL) == MHD_YES);
  if (!flags) {
    fprintf(stderr,
            "Invalid FORGE_WEB_POLL: use auto, epoll, poll or select\n");
    return 1;
  }
  /* A synchronous handler must not block other connections sharing its poller.
   * MHD's connection threads support poll/select, but not epoll or a pool. */
  if (connection_threads) {
    if (flags & MHD_USE_EPOLL) {
      flags &= ~MHD_USE_EPOLL;
      if (MHD_is_feature_supported(MHD_FEATURE_POLL) == MHD_YES)
        flags |= MHD_USE_POLL;
    }
    flags |= MHD_USE_THREAD_PER_CONNECTION | MHD_USE_ITC;
  }
  struct MHD_Daemon *d = start_daemon(flags, &addr, (unsigned)workers, connection_threads);
  if (!d && (flags & (MHD_USE_EPOLL | MHD_USE_POLL))) {
    flags = MHD_USE_INTERNAL_POLLING_THREAD | MHD_USE_ERROR_LOG |
            (connection_threads ? MHD_USE_THREAD_PER_CONNECTION | MHD_USE_ITC : 0);
    d = start_daemon(flags, &addr, (unsigned)workers, connection_threads);
  }
  if (!d) {
    return 1;
  }
  fprintf(stderr, "Forge portfolio API listening on %s:%lld (threads=%s, polling=%s)\n",
          host, (long long)port, threads,
          flags & MHD_USE_EPOLL  ? "epoll"
          : flags & MHD_USE_POLL ? "poll"
                                 : "select");
  while (!stopping) {
    struct timespec delay = {0, 100000000};
    nanosleep(&delay, NULL);
  }
  MHD_stop_daemon(d);
  return 0;
}

const char *fw_normalize_ip(const char *ip) {
  struct in_addr a;
  struct in6_addr b;
  char result[INET6_ADDRSTRLEN];
  if (inet_pton(AF_INET, ip, &a) == 1) {
    inet_ntop(AF_INET, &a, result, sizeof(result));
    return copy(result);
  }
  if (inet_pton(AF_INET6, ip, &b) == 1) {
    if (IN6_IS_ADDR_V4MAPPED(&b))
      inet_ntop(AF_INET, &b.s6_addr[12], result, sizeof(result));
    else
      inet_ntop(AF_INET6, &b, result, sizeof(result));
    return copy(result);
  }
  return "";
}
int64_t fw_sort(int64_t array, const char *key) {
  if (fw_kind(array) != 5)
    return 0;
  size_t count = (size_t)fw_count(array);
  for (size_t i = 1; i < count; i++) {
    size_t j = i;
    while (j > 0) {
      struct json_object *a =
          json_object_array_get_idx(P(struct json_object, array), j - 1);
      struct json_object *b =
          json_object_array_get_idx(P(struct json_object, array), j);
      if (strcasecmp(fw_text(fw_get(H(a), key)), fw_text(fw_get(H(b), key))) <=
          0)
        break;
      json_object_get(a);
      json_object_get(b);
      json_object_array_put_idx(P(struct json_object, array), j - 1, b);
      json_object_array_put_idx(P(struct json_object, array), j, a);
      j--;
    }
  }
  return 1;
}
typedef struct {
  int64_t urls;
  const char *bearer;
  char **results;
  size_t next, count;
  pthread_mutex_t mutex;
} FetchBatch;
static void *fetch_worker(void *arg) {
  FetchBatch *batch = arg;
  for (;;) {
    pthread_mutex_lock(&batch->mutex);
    size_t i = batch->next++;
    pthread_mutex_unlock(&batch->mutex);
    if (i >= batch->count)
      break;
    fw_scope_begin();
    int64_t value = fw_fetch(fw_text(fw_at(batch->urls, (int64_t)i)), "GET", "",
                             batch->bearer);
    batch->results[i] = strdup(fw_dump(value));
    fw_scope_end();
  }
  return NULL;
}
int64_t fw_fetch_many(int64_t urls, const char *bearer) {
  int64_t out = fw_array();
  size_t count = (size_t)fw_count(urls);
  if (!count || count > 300)
    return out;
  char **results = calloc(count, sizeof(char *));
  if (!results)
    return out;
  FetchBatch batch = {
      .urls = urls, .bearer = bearer, .results = results, .count = count};
  pthread_mutex_init(&batch.mutex, NULL);
  pthread_t threads[4];
  size_t started = 0;
  for (size_t i = 0; i < 4; i++) {
    if (pthread_create(&threads[started], NULL, fetch_worker, &batch) == 0)
      started++;
  }
  if (!started) {
    for (size_t i = 0; i < count; i++)
      fw_push(out,
              fw_fetch(fw_text(fw_at(urls, (int64_t)i)), "GET", "", bearer));
  } else {
    for (size_t i = 0; i < started; i++)
      pthread_join(threads[i], NULL);
    for (size_t i = 0; i < count; i++) {
      fw_push(out, fw_parse(results[i]));
      free(results[i]);
    }
  }
  pthread_mutex_destroy(&batch.mutex);
  free(results);
  return out;
}

int64_t fw_has(int64_t h, const char *key) {
  struct json_object *value = NULL;
  return fw_kind(h) == 4 &&
         json_object_object_get_ex(P(struct json_object, h), key, &value);
}
const char *fw_cookie(int64_t request, const char *name) {
  const char *s = fw_header(request, "Cookie");
  size_t length = strlen(name);
  while (*s) {
    while (*s == ' ' || *s == ';')
      s++;
    const char *end = strchr(s, ';');
    size_t count = end ? (size_t)(end - s) : strlen(s);
    if (count > length && !strncmp(s, name, length) && s[length] == '=')
      return track(strndup(s + length + 1, count - length - 1), 0);
    if (!end)
      break;
    s = end + 1;
  }
  return "";
}
int64_t fw_set_cookie(int64_t request, const char *name, const char *value,
                      int64_t age, int64_t secure) {
  Request *r = P(Request, request);
  if (!r || !r->response || !name || !*name || !value || age < 0 || age > 86400)
    return 0;
  for (const char *p = name; *p; p++)
    if (!(isalnum((unsigned char)*p) || *p == '_' || *p == '-'))
      return 0;
  for (const char *p = value; *p; p++)
    if (!(isalnum((unsigned char)*p) || strchr("_-.", *p)))
      return 0;
  char buffer[1024];
  if (snprintf(buffer, sizeof(buffer),
               "%s=%s; Max-Age=%lld; Path=/api/auth/github; HttpOnly; "
               "SameSite=Lax%s",
               name, value, (long long)age,
               secure ? "; Secure" : "") >= (int)sizeof(buffer))
    return 0;
  return MHD_add_response_header(r->response, "Set-Cookie", buffer) == MHD_YES;
}
