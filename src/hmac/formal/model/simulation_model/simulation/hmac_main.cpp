#include "systemc.h"
#include "Interfaces.h"
#include "../../hmac_core.h"
#include "hmac_tests.h"
#include "../top.h"
#include "../sha_algo_masked.h"

int sc_main(int argc, char **argv) {
  top top1("top1");
  hmac_tests tests("tests");


   Blocking<block> hmac_msg("hmac_msg");
   Blocking<sc_biguint<KEY_WIDTH>> tag("tag");

  top1.top_hmac(hmac_msg);
  top1.top_tag(tag);

  tests.hmac_msg(hmac_msg);
  tests.tag(tag);
  

  sc_start();
  return 0;
}
