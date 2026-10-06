#include "../src/bridge.c"
#include <assert.h>
#include <string.h>

static char *signed_raw(const char *header, const char *payload) {
  char *h = b64((const unsigned char *)header, strlen(header));
  char *p = b64((const unsigned char *)payload, strlen(payload));
  size_t size = strlen(h) + strlen(p) + 2;
  char *message = track(malloc(size), 0);
  assert(message);
  snprintf(message, size, "%s.%s", h, p);
  unsigned char mac[32];
  unsigned length;
  assert(HMAC(EVP_sha256(), "test-secret", 11, (unsigned char *)message,
              strlen(message), mac, &length));
  char *signature = b64(mac, length);
  char *token = track(malloc(strlen(message) + strlen(signature) + 2), 0);
  assert(token);
  sprintf(token, "%s.%s", message, signature);
  return token;
}
static void json_security(void) {
  const char *bad[] = {"{\"role\":\"user\",\"role\":\"admin\"}",
                       "{\"role\":\"user\",\"r\\u006fle\":\"admin\"}",
                       "{\"n\":{\"x\":1,\"x\":2}}",
                       "[{\"x\":1,\"x\":2}]",
                       "{\"key\\u0000suffix\":1}",
                       "{\"role\":\"admin\\u0000user\"}",
                       "[\"value\\u0000suffix\"]",
                       "{\"key\":9223372036854775808}",
                       "-9223372036854775809",
                       "18446744073709551615",
                       "1e309"};
  for (size_t i = 0; i < sizeof(bad) / sizeof(bad[0]); i++)
    assert(!fw_parse(bad[i]));
  int64_t value = fw_parse(
      "{\"key\":\"literal "
      "\\\\u0000\",\"other\":{\"key\":1},\"array\":[{\"key\":2},{\"key\":3}]}");
  assert(value);
  assert(!strcmp(fw_text(fw_get(value, "key")), "literal \\u0000"));
  assert(fw_integer(fw_parse("9223372036854775807")) == INT64_MAX);
  assert(fw_integer(fw_parse("-9223372036854775808")) == INT64_MIN);
  assert(fw_parse("{\"한글\":1,\"emoji\\ud83d\\ude00\":2}"));
  assert(!fw_parse("{\"한글\":1,\"\\ud55c\\uae00\":2}"));
  /* Shared member names in sibling objects remain legal. */
  assert(fw_parse("[{\"x\":1},{\"x\":2}]"));
  /* Real UTF-8 in outbound README JSON failed under Alpine/json-c 0.18. */
  int64_t unicode = fw_parse("{\"readme\":\"line\\n2.32× 한글 😀\",\"owner_id\":\"999\"}");
  assert(unicode);
  assert(!strcmp(fw_text(fw_get(unicode, "readme")), "line\n2.32× 한글 😀"));
  assert(!strcmp(fw_text(fw_parse("\"é한😀\"")), "é한😀"));
  assert(fw_parse("{\"é\":1,\"€\":2,\"😀\":3}"));
  assert(!fw_parse("{\"é\":1,\"\\u00e9\":2}"));
  assert(!fw_parse("{\"😀\":1,\"\\ud83d\\ude00\":2}"));
  assert(!fw_parse("{\"한글\":\"😀\\u0000suffix\"}"));
  assert(!fw_parse("[é]"));
  assert(!fw_parse("{\"x\":\"😀\",}"));
  assert(!fw_parse("{\"x\":\"😀\"} /* comment */"));
  const char *invalid_utf8[] = {
      "{\"x\":\"\x80\"}", "{\"x\":\"\xc0\xaf\"}",
      "{\"x\":\"\xe0\x80\xaf\"}", "{\"x\":\"\xed\xa0\x80\"}",
      "{\"x\":\"\xf0\x80\x80\xaf\"}", "{\"x\":\"\xf4\x90\x80\x80\"}",
      "{\"x\":\"\xc3\"}", "{\"x\":\"\xe2\x82\"}"
  };
  for (size_t i = 0; i < sizeof invalid_utf8 / sizeof invalid_utf8[0]; i++)
    assert(!fw_parse(invalid_utf8[i]));

}
static void jwt_security(void) {
  char payload[256];
  snprintf(payload, sizeof(payload),
           "{\"sub\":\"tester\",\"role\":\"user\",\"exp\":%lld}",
           (long long)fw_now() + 3600);
  char *token = signed_raw("{\"alg\":\"HS256\"}", payload);
  assert(fw_jwt_verify(token, "test-secret"));
  assert(!fw_jwt_verify(token, "wrong-secret"));
  assert(
      !fw_jwt_verify(signed_raw("{\"alg\":\"none\"}", payload), "test-secret"));
  assert(!fw_jwt_verify(
      signed_raw("{\"alg\":\"none\",\"alg\":\"HS256\"}", payload),
      "test-secret"));
  assert(!fw_jwt_verify(signed_raw("{\"alg\":\"HS256\\u0000other\"}", payload),
                        "test-secret"));
  assert(!fw_jwt_verify(
      signed_raw("{\"alg\":\"HS256\",\"crit\":[\"unknown\"]}", payload),
      "test-secret"));
  assert(!fw_jwt_verify(
      signed_raw("{\"alg\":\"HS256\",\"b64\":false}", payload), "test-secret"));
  const char *bad[] = {
      "{\"sub\":\"tester\",\"role\":\"user\",\"exp\":18446744073709551615}",
      "{\"sub\":\"tester\",\"role\":\"user\",\"exp\":9999999999.0}",
      "{\"sub\":\"tester\",\"role\":\"user\",\"exp\":\"9999999999\"}",
      "{\"sub\":\"tester\",\"role\":\"user\",\"exp\":9999999999,\"nbf\":"
      "9999999999}",
      "{\"sub\":\"tester\",\"role\":\"user\",\"exp\":9999999999,\"nbf\":\"0\"}",
      "{\"sub\":\"tester\",\"role\":\"user\",\"role\":\"admin\",\"exp\":"
      "9999999999}",
      "{\"sub\":\"tester\",\"role\":\"admin\\u0000user\",\"exp\":9999999999}"};
  for (size_t i = 0; i < sizeof(bad) / sizeof(bad[0]); i++)
    assert(!fw_jwt_verify(signed_raw("{\"alg\":\"HS256\"}", bad[i]),
                          "test-secret"));
  /* HS256's final base64url digit has two unused bits; changing them must
   * not create another accepted spelling of the same signed token. */
  char *alternate = track(strdup(token), 0);
  const char *alphabet =
      "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";
  char *last = alternate + strlen(alternate) - 1;
  const char *position = strchr(alphabet, *last);
  assert(position && !((position - alphabet) & 3));
  *last = alphabet[(position - alphabet) | 1];
  assert(!fw_jwt_verify(alternate, "test-secret"));
  char large[16386];
  memset(large, 'a', sizeof(large) - 1);
  large[sizeof(large) - 1] = 0;
  assert(!fw_jwt_verify(large, "test-secret"));
}
static void proxy_security(void) {
  ProxyNetwork network;
  assert(parse_proxy_network("192.0.2.0/24", &network));
  struct sockaddr_in peer = {.sin_family = AF_INET};
  assert(inet_pton(AF_INET, "192.0.2.42", &peer.sin_addr) == 1);
  assert(configure_proxies(""));
  assert(!trusted_peer((struct sockaddr *)&peer));
  assert(configure_proxies(" 192.0.2.0/24, ::1/128 "));
  assert(trusted_peer((struct sockaddr *)&peer));
  assert(inet_pton(AF_INET, "192.0.3.42", &peer.sin_addr) == 1);
  assert(!trusted_peer((struct sockaddr *)&peer));
  assert(configure_proxies("192.0.3.42"));
  assert(trusted_peer((struct sockaddr *)&peer));
  struct sockaddr_in6 peer6 = {.sin6_family = AF_INET6};
  assert(inet_pton(AF_INET6, "2001:db8:abcd::42", &peer6.sin6_addr) == 1);
  assert(configure_proxies("2001:db8:abcd::/48"));
  assert(trusted_peer((struct sockaddr *)&peer6));
  assert(inet_pton(AF_INET6, "2001:db8:abce::42", &peer6.sin6_addr) == 1);
  assert(!trusted_peer((struct sockaddr *)&peer6));
  const char *bad[] = {
      "127.0.0.1,",          "127.0.0.1,,::1",     "127.0.0.1/33",  "::1/129",
      "127.0.0.1/-1",        "127.0.0.1/",         "127.0.0.1/8/8", "localhost",
      "127.0.0.1,malformed", "0.0.0.0/99999999999"};
  for (size_t i = 0; i < sizeof(bad) / sizeof(bad[0]); i++) {
    assert(!configure_proxies(bad[i]));
    assert(trusted_proxy_count == 0);
  }
}
int main(void) {
  fw_scope_begin();
  json_security();
  jwt_security();
  proxy_security();
  fw_scope_end();
  return 0;
}
