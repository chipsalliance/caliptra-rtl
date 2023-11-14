// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// Description:
//

#ifndef HMAC_CORE_TESTS_H
#define HMAC_CORE_TESTS_H


#include "systemc.h"
#include "Interfaces.h"
#include <fstream>
#include <string>
#include "../sha_algo_masked.h"
#include "../../hmac_core.h"
//#include "../top.h"

using namespace std;


SC_MODULE(hmac_tests) {
public:
  SC_CTOR(hmac_tests) {
   // read_test_vectors(file_path);
    SC_THREAD(testbench)
  }

  blocking_out <block> hmac_msg;
  blocking_in<sc_biguint<384>> tag;

private:
  void testbench() {

    sc_biguint<384> test_result;
    block test_input;
    sc_biguint<384>KEY;
    string COUNT;
    sc_biguint<104000> MSG_raw; 
    sc_biguint<104000> MSG_padded; 
    sc_uint<32>  MSG_Length;
    sc_biguint<384> expected_result;
    int num = 1;
    int zero_pad_len, MSG_chnks,i;
    /* std::string filename = "hmac_vectors_singleblk.txt";
    //std::ifstream myfile;

    std::ifstream myfile(filename);

    if (!myfile.is_open()) {
    std::cout << "Failed to open the file: " << filename << std::endl;
    // Handle the error condition
    return;
}
    while (myfile)
    {
      myfile >> COUNT;
      myfile >> MSG_Length;
      myfile >> std::hex >> KEY;
      myfile >> std::hex >> MSG_padded;
      myfile >> expected_result;
     

      MSG_chnks = static_cast<int> (MSG_Length / 1024);  */
    while(true){
      test_input.init = 1;
      test_input.next = 0;
      test_input.key = 0;
      MSG_padded = "0x01010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010100768412320f7b0aa5812fce428dc4706b3cae50e02a64caa16a782249bfe8efc4b7ef1ccb126255d196047dfedf17a0a96b9d3dad2e1b8c1c05b19875b6659f4de23c3b667bf297ba9aa47740787137d896d5724e4c70a825f872c9ea60d2edf5800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000888";
      expected_result = 0;
      MSG_Length = 2048;
      MSG_chnks = static_cast<int> (MSG_Length / 1024); 
      
      for (i=0; i <MSG_chnks; i++) {   
        test_input.block_msg = static_cast<sc_biguint<1024>>(MSG_padded >> (1024*(MSG_chnks-1)));
        cout<<MSG_chnks<<endl;
        cout<<"init,next: "<<test_input.init<<","<<test_input.next<<endl;
        if (i>0){
          test_input.next = 1;
          test_input.init = 0;}
        hmac_msg->write(test_input);  
        MSG_padded = static_cast<sc_biguint<104000>> (MSG_padded << 1024);
        test_input.init = 0;
        tag->read(test_result, "success");
        
      }; 
 
      if (test_result != (expected_result)){ 
        std::cout << "Test " << COUNT << " Failed!" << std::endl;
        std::cout << std::hex << "Output:   " << test_result << std::endl;
        std::cout << std::hex << "Expected: " << expected_result << std::endl;
      } 
      else {
          std::cout << "Test " << COUNT << " Passed!" << std::endl;
      }

      
    

    //myfile.close();
    sc_stop();
}
  }
};


#endif






