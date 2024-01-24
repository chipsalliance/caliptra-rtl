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

#ifndef TB_H
#define TB_H


#include "systemc.h"
#include "../Interfaces/Interfaces.h"
#include <fstream>
#include <string>
#include "../sha512.h"

SC_MODULE(testbench) {
public:
  SC_CTOR(testbench) {
   // read_test_vectors(file_path);
    SC_THREAD(tests)
  }

  blocking_out <SHA_Args> in_testdata;
  slave_in<sc_biguint<512>> out_testdata;

private:
  void tests() {

    wait(0, SC_PS);

    sc_biguint<512> test_result;
    SHA_Args test_input;
    sc_biguint<104000> MSG_raw; 
    sc_biguint<104000> MSG_padded; 
    sc_uint<32>  MSG_Length;
    sc_biguint<512> expected_result;
    int num = 1;
    int zero_pad_len, MSG_chnks,i; 
    bool success = false;
    std::string line;
    std::ifstream myfile;

    myfile.open ("./testvectors/512_long_msg.txt");
    
    while (myfile)
    {
      myfile >> MSG_Length;
      myfile >> std::hex >> MSG_raw;
      myfile >> expected_result;
     
      zero_pad_len = (896 - MSG_Length - 1) % 1024;
      MSG_chnks = static_cast<int> ((MSG_Length + 1 + 128 +  zero_pad_len) / 1024); 
      MSG_padded = static_cast<sc_biguint<104000>> (static_cast<sc_biguint<104000>> (MSG_raw << (1 + 128 +  zero_pad_len)) + (static_cast<sc_biguint<104000>> (8) << ((125 + zero_pad_len))) + static_cast<sc_biguint<104000>> (MSG_Length));      

      test_input.SHA_Mode = 512;
      test_input.init = 1;
      test_input.next = 0;

      //To Do: use   assert ( parsed.hasError == false ) instead
      for (i=0; i <MSG_chnks; i++) {   
         
        test_input.in = static_cast<sc_biguint<1024>>(MSG_padded >> (1024*(MSG_chnks-1)));
        if (i>0)
          test_input.next = 1;
        in_testdata->write(test_input);  
        MSG_padded = static_cast<sc_biguint<104000>> (MSG_padded << 1024);
        test_input.init = 0;
        success = false;
        while(!success)
        {
          wait(0, SC_PS);
          out_testdata->slave_read(test_result, success);
        }
        
      };

      if (test_result != expected_result){ 
        std::cout << "Test " << num++ << " Failed!" << std::endl;
        std::cout << std::hex << "Output:   " << test_result << std::endl;
        std::cout << std::hex << "Expected: " << expected_result << std::endl;
        //sc_stop();
      } 
      else {
          std::cout << "Test " << num++ << " Passed!" << std::endl;
      }

      
    }

    myfile.close();
    sc_stop();

  }
};


#endif

