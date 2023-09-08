// -------------------------------------------------
// Contact: contact@lubis-eda.com
// Author: Tobias Ludwig, Michael Schwarz
// -------------------------------------------------
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

#ifndef SHA256_CORE_TESTS_H
#define SHA256_CORE_TESTS_H

#include "systemc.h"
#include "Interfaces.h"
#include <iomanip>
#include <string>
#include <array>
#include <iostream>
#include <chrono>
#include <cstring>
#include <sstream>

SC_MODULE(sha256_core_tests)
{
public:
  SC_CTOR(sha256_core_tests)
  {

    SC_THREAD(tests);
  }
  blocking_out< int> out_mode;
  blocking_out<std::string> in_block; // Original type: 'wire [511:0]'
  blocking_in<std::string> out_block; // Original type: 'wire [255:0]'

private:
  void tests()
  {
    std::string in, out;
    out_mode->write(0);
    in = "Hello world";
    in_block->write(in);
    out_block->read(out);
    if (out == "64ec88ca00b268e5ba1a35678a1b5316d212f4f366b2477232534a8aeca37f3c")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Lubis EDA";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "d97541dcee8f0a27ff699624c553512f00e0d0096d1abd84e4272389d869678d")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Tu Kaiserslautern";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "28742eba07604f9d3d3b46870ab1d16225e129a86047c50d113222776de1768b")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Mostafa Elnahas";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "2f001374ae549a41a9235c4e4f4d07431219218dbe557d8f3295c6da09253cc0")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Tobias Ludwig";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "236244ccdbabb40dc5624dd44da2ea97b4aea5a950dc7ee3454d138b34bd7d9d")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Lubis EDA";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "d97541dcee8f0a27ff699624c553512f00e0d0096d1abd84e4272389d869678d")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "5145";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "766af62a6275002e9909af31d1f15e02609d9443de336c0ce13ba52cb3e56042")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }
    in = "Michael Shwarz";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "bd94211bd6edc570c1b6ab198b22b3562d658f1585a950a7f5d05171ba16c780")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Max";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "a1a5936d3b0f8a69fd62c91ed9990d3bd414c5e78c603e2837c65c9f46a93eb8")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Tim";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "aac09a648fc382b6f78897595486e691d00de9dfc742f3ba1930464b56eecda6")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Tom";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "81f3bf42a93cf18dece9321ac5c93313126eb5ca92164d74643e4cbf60ecde9c")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Luiz";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "0dd0029404cbe8bbad2cd84ec0f5089e4ca29d46719323b15595ffa765a88ffe")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Advaith";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "28c37e54d13bf521c4967aa26c30750b9703ba35bf27e2d2cff2933f48029abb")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Sandeep";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "b22db2a12b26ae466aa309491c247b7e517ca9502c6005310dc642eb96ab3c19")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Rohith";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "49e4d11bf1c03edc1c3804381a1fb6b9dbaa18b2264abe2ec05b91a9d633b587")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Christian";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "67e0082893e848c8706431c32dea6c3ca86c488ae24ee6b0661489cb8b3bb78a")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Kathrin";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "d89a423ad0035508ac3cc7a7525a379f28e06c3527ffa3d1562b97a074ea4472")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Fatemeh";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "6aa81ce731a2cfb14016b63d4803642a0fc616b0838892bbf77de7d12105bbdc")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Lilo";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "6ef693f0db886ad4bf27c4d0a77c7d9ad74300211c438689a70c5f0461c79694")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Stitch";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "acc870db91ebe17c3c5d593c244f9a1b1593c4d3d6509846618702f6fbf1047b")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    ;
    in = "Goofy";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "ba89bbde79460200e4aeb0f6ea27e4a304adf58853f9ad124aa66726710463d8")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Pluto";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "8dad5f6a7dd2dcd8c35ec2fd7babb499bcad60d27d73fe73eca2ce025dfd3b47")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Donald duck";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "49d2118f9e78d5dcbafbdf0e6fd3979bc4d38ad26736ec2733e480e51e374778")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "aeriel";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "6179fc95ef559edb65dc55f565718c9e13167e774dc78c1f8687495ba98b8ead")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Mulan";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "cbaa9fe121b76892d534db5412b1082cf35c417ad7f2de572149a1eaf17789ac")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Woody";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "08bb39b964dcab376f5862d7e9c8f34b8f96cfaf380142246631d78178986125")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Buzz Alrdrin";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "45883804cf4f2f87688af4c94780dd4fa59a59d6f82c00ba490d4c732b6ec0e4")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Mickey Mouse";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "ac752a50e0f6d3cdecb914d6f4fe52250ac5a8ab7238e6b7b9cef0f4b6daf652")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Mini Mouse";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "b5b85dc31e212989ceef783a24098d92d98ce1d8c97e3842fc2694c514ac3cbe")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Simba";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "f9c552cca49d95db9e09a876bbd74eb833ee063e5ce058d121d53ad0271cedc4")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Mufasa";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "de83276e6b45237548b7d6c990b6fe6fd55de68a725e9ddeaf35666f7d93c475")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Scar";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "ed82f3944eeda21207da3b2214f58830ed56d728c0161297ccc03dea247102c2")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Timon";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "f2cc6496143be1714a909f7c955ccb82bf0aaefa6505a49cf3409dc1e789fdcc")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Nala";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "aa6a77d9ccef603ca1a6e07ea856d85d067f69d1fa94f01cf22cdfafd1777255")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Alaa Eldin";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "01570ab379e65f32949f55a29af26c885409e6db1b2dce9c1b6fa9f268e32df6")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Genie";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "bc8359eb1335ec654b14ddb264bdcaa1ffe6ebebe431ebb2c2ede4552026a8c2")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Winnie";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "168bb5b349fe144916def9f699ef4544353b89728aa377822a469274388b141b")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Piglet";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "d9b336af11e4299f3b75110fe04bbf8ccc99f8bd3e50f38db9614d7486bfefed")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Hercules";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "ef97a66f04394990d341c2a51eab11d6490d90f92318b50cc02988bd5fde0d88")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Zeus";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "0ff0ef099ecb754b08b36053f2a8327f0d5b470cc3656c9fd043b9d1a2d719f5")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Tigger";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "49df5f6cae1d5191dfbf17a3696ef9818ee5bc9b11e5179afe21f0a23f9e385e")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "philoctetes";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "1d321e3644f7384f47f6df2a7e8eebaf14f417d5b6d0cc20c8b1cd6d9f6b25a5")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "A";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "559aead08264d5795d3909718cdd05abd49572e84fe55590eef31a88a08fdffd")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "AB";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "38164fbd17603d73f696b8b4d72664d735bb6a7c88577687fd2ae33fd6964153")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "ABC";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "b5d4045c3f466fa91fe2cc6abe79232a1a57cdf104f7a26e716e0a1e2789df78")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "ABCDE";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "f0393febe8baaa55e32f7be2a7cc180bf34e52137d99e056c817a9c07b8f239a")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "ABCDEF";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "e9c0f8b575cbfcb42ab3b78ecc87efa3b011d9a5d10b09fa4e96f240bf6a82f5")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "ABCDEFG";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "e9a92a2ed0d53732ac13b031a27b071814231c8633c9f41844ccba884d482b16")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "ABCDEFGH";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "9ac2197d9258257b1ae8463e4214e4cd0a578bc1517f2415928b91be4283fc48")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "ABCDEFGHI";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "2cdf6e152315e807562e3265bea43b48fe82511242d002fc45a35d190067a3d0")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "ABCDEFGHIJ";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "261305762671a58cae5b74990bcfc236c2336fb04a0fbac626166d9491d2884c")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "ABCDEFGHIJK";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "62ee2337525d8cf6e6529cf8579d51191555cb32c033c903bedb8ca295e03f81")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "ABCDEFGHIJKL";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "922429ccdb7045d11143e2e3982a11afc11b537bf259d88d2425fa8806e86e78")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "ABCDEFGHIJKLM";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "170f5660fece35db218fece184b25e99771ddb3e8852850aba6f237624341ff4")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "N";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "8ce86a6ae65d3692e7305e2c58ac62eebd97d3d943e093f577da25c36988246b")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "NO";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "23794d91c53ae875c8e247d72561e35d9d06ee07c70c9e0dbcc977a6d161504a")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "NOP";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "692b4856a5ca2f45e38d56256b64b254865b31069ffe891f4e7876c9075f6b10")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "NOPQ";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "0006b627f94247c2991955b58be1821c649c649e4fdf445469bebc3762919d2d")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "NOPQR";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "29259343584eee776b38f7b89ddcee6b72a1aa71ee4aa9dc5d655a8ec8289ca7")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "NOPQRS";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "12be4169c73bf011b81f405d6b7f8bbf897d42a94fd4b88282efe3a2d100aa02")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "NOPQRST";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "20d5fd7f8e1f2f1b4656153a4800a04ea6d5c70dc7b24ea0b593ea13053232f8")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "NOPQRSTW";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "68201bf9788c3be4a6f411b95202ffcf3a40fa15bdd6074160a7ee1465cb25aa")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "NOPQRSTWX";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "233d4813648dd26e37304cb8c0c18ffeae60a656f6b95395a9068a6df0643149")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "XYZ";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "ade099751d2ea9f3393f0f32d20c6b980dd5d3b0989dea599b966ae0d3cd5a1e")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Super-Man";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "eef32a6ad13cd7ce249a66eedfebfdc019d3a07946029dc82bd60feff083aecf")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "BatMan";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "1175f8ee115c0a5da53eccfd2c852c4ee0c5fb513ce2d71f0c4a69c2faf370da")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "CatWoman";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "690aa6b8a7aa834ba0137fa8efbf4ce8287dbae06e2d0c1bab01142558d1a53d")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }

    in = "Jadal";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "32ffebd23525c0424caa9aac71dcb26e66fd891ae28a8da6de5cf1761e00eacb")
      cout << "test passed " << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }
    in = "Jadal";
    out_mode->write(1);
    in_block->write(in);
    out_block->read(out);
    if (out == "5296ec14dd94b33683767b95b2d83078647f3aa082be16a8b975a9a5")
    {
      cout << "test passedsha224" << endl;
    }
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }
    in = "Einstien";
    out_mode->write(0);

    in_block->write(in);
    out_block->read(out);
    if (out == "7a287e7aab0d8218a74531bdcc1ad83fd5fef954e67c66d346d1e51e6be0f66b")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }
    in = "ad9dbaff7b64c8a7124d49712c962c1adc1295c311ec04b8b013bb3ad709d897ad9dbaff7b64c8a7124d49712c962c1adc1295c311ec04b8b013bb3ad709d897ad9dbaff7b64c8a7124d49712c962c1adc1295c311ec04b8b013bb3ad709d897ad9dbaff7b64c8a7124d49712c962c1adc1295c311ec04b8b013bb3ad709d897";
    out_mode->write(0);
    in_block->write(in);
    out_block->read(out);
    if (out == "126f5f6829b04b22bbe37812955030fa4bb94aad0c853356857b3d2cdd138438")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }
/*

    in = "ad9dbaff7b64c8a7124d49712c962c1adc1295c311ec04b8b013bb3ad709d897ad9dbaff7b64c8a7124d49712c962c1adc1295c311ec04b8b013bb3ad709d897ad9dbaff7b64c8a7124d49712c962c1adc1295c311ec04b8b013bb3ad709d897ad9dbaff7b64c8a7124d49712c962c1adc1295c311ec04b8b013bb3ad709d897";
    out_mode->write(0);
    in_block->write(in);
    out_block->read(out);
    if (out == "abd613f1556aa411e2008c61b3045ab1e56a798494685993ffdc66d8")
      cout << "test passed" << endl;
    else
    {
      cout << out << endl;
      cout << "test failed" << endl;
    }*/
  }
};

#endif
