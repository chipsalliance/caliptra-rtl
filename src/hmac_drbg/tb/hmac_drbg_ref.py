import hmac
import hashlib
class HMAC_DRBG:
   def __init__(self, entropy, nonce=b"", personalization=b""):
       """
       Instantiates HMAC-DRBG with entropy, nonce, and optional personalization string.
       """
       self.hash_function = hashlib.sha384
       self.seed_length = self.hash_function().digest_size 
       self.K = b"\x00" * self.seed_length
       self.V = b"\x01" * self.seed_length
       seed_material = entropy + nonce + personalization
       self.update(seed_material)
   def _hmac(self, key, data):
       """ Computes HMAC. """
    #    print("key=", key.hex())
    #    print("val=", data.hex())
    #    print("dig=", hmac.new(key, data, self.hash_function).digest().hex(),'\n')
       return hmac.new(key, data, self.hash_function).digest()
   def update(self, seed_material=b""):
       """
       Updates the internal state with new seed material.
       """
       self.K = self._hmac(self.K, self.V + b"\x00" + seed_material)
       self.V = self._hmac(self.K, self.V)
       if seed_material:
           self.K = self._hmac(self.K, self.V + b"\x01" + seed_material)
           self.V = self._hmac(self.K, self.V)
   def reseed(self, additional_entropy):
       """ Reseeds the DRBG with new entropy. """
       self.update(additional_entropy)
   def generate(self, num_bytes, additional_input=b""):
       """
       Generates `num_bytes` random bytes.
       """
       if additional_input:
           self.update(additional_input)
       output = b""
       while len(output) < num_bytes:
           self.V = self._hmac(self.K, self.V)
           output += self.V
       self.update(additional_input)
       return output[:num_bytes]
   
def cavp_no_reseed_test(COUNT, entropy, nonce, personalization, additional_input0, additional_input1, returnedbits_len, expected):
    returnedbits_len_inbyte = int(returnedbits_len / 8)
    drbg = HMAC_DRBG(entropy, nonce, personalization)
    # print("INSTANTIATED V=", drbg.V.hex())
    # print("INSTANTIATED K=", drbg.K.hex())
    random_bytes = drbg.generate(returnedbits_len_inbyte, additional_input0)
    # print("FIRST CALL V=", drbg.V.hex())
    # print("FIRST CALL K=", drbg.K.hex())
    # print("first output=",random_bytes.hex())  # Output random data in hex
    random_bytes = drbg.generate(returnedbits_len_inbyte, additional_input1)
    # print("Second CALL V=", drbg.V.hex())
    # print("Second CALL K=", drbg.K.hex())
    # print("second output=",random_bytes.hex())  # Output random data in hex
    result = (random_bytes == expected)
    print("CAVP test number", COUNT,"=", result)
    return result

def caliptra_test(COUNT, entropy, nonce, expected0, expected1=b"", expected2=b""):
    returnedbits_len_inbyte = int(384 / 8)
    drbg = HMAC_DRBG(entropy, nonce)
    # print("INSTANTIATED V=", drbg.V.hex())
    # print("INSTANTIATED K=", drbg.K.hex())
    random_bytes = drbg.generate(returnedbits_len_inbyte)
    # print("FIRST CALL V=", drbg.V.hex())
    # print("FIRST CALL K=", drbg.K.hex())
    # print("first output=",random_bytes.hex())  # Output random data in hex
    result = (random_bytes == expected0)
    print("Caliptra INIT test number", COUNT,"=", result)
    if (expected1):
        random_bytes = drbg.generate(returnedbits_len_inbyte)
        # print("Second CALL V=", drbg.V.hex())
        # print("Second CALL K=", drbg.K.hex())
        # print("second output=",random_bytes.hex())  # Output random data in hex
        result = (random_bytes == expected1)
        print("Caliptra NEXT test number", COUNT,"=", result)
        if (expected2):
            random_bytes = drbg.generate(returnedbits_len_inbyte)
            # print("Third CALL V=", drbg.V.hex())
            # print("Third CALL K=", drbg.K.hex())
            # print("Third output=",random_bytes.hex())  # Output random data in hex
            result = (random_bytes == expected2)
            print("Caliptra NEXT test number", COUNT,"=", result)
    return result

def cavp_test_vectors():
    """
       from: https://github.com/coruus/nist-testvectors/blob/master/csrc.nist.gov/groups/STM/cavp/documents/drbg/drbgtestvectors/drbgvectors_no_reseed/HMAC_DRBG.rsp
    """

    ReturnedBitsLen = 1536

    COUNT = 0
    EntropyInput = bytes.fromhex("a1dc2dfeda4f3a1124e0e75ebfbe5f98cac11018221dda3fdcf8f9125d68447a")
    Nonce =  bytes.fromhex("bae5ea27166540515268a493a96b5187")
    PersonalizationString = bytes.fromhex("")
    AdditionalInput0 = bytes.fromhex("")
    AdditionalInput1 = bytes.fromhex("")
    ReturnedBits = bytes.fromhex("228293e59b1e4545a4ff9f232616fc5108a1128debd0f7c20ace837ca105cbf24c0dac1f9847dafd0d0500721ffad3c684a992d110a549a264d14a8911c50be8cd6a7e8fac783ad95b24f64fd8cc4c8b649eac2b15b363e30df79541a6b8a1caac238949b46643694c85e1d5fcbcd9aaae6260acee660b8a79bea48e079ceb6a5eaf4993a82c3f1b758d7c53e3094eeac63dc255be6dcdcc2b51e5ca45d2b20684a5a8fa5806b96f8461ebf51bc515a7dd8c5475c0e70f2fd0faf7869a99ab6c")
    cavp_no_reseed_test(COUNT, EntropyInput, Nonce, PersonalizationString, AdditionalInput0, AdditionalInput1, ReturnedBitsLen, ReturnedBits)

    COUNT = 1
    EntropyInput = bytes.fromhex("067fa0e25d71ea392671c24f38ef782ab3587a7b3c77ea756f7bd496b445b7a3")
    Nonce = bytes.fromhex("ce6acc722768ca0e03784b2217bc60e4")
    PersonalizationString = bytes.fromhex("")
    AdditionalInput0 = bytes.fromhex("")
    AdditionalInput1 = bytes.fromhex("")
    ReturnedBits = bytes.fromhex("16eaa49510ffad8cc21ec32858640a0d6f34cb03e8649022aa5c3f566b44e8ace7c3b056cf2a44b242de09ae21dba4275418933611875841b4f0944a8272848c5dc1aad685935e12511d5ee27e9162d4bb968afab53c4b338269c1c77da9d78617911ed4390cb20e88bf30b74fda66fe05df5537a759061d3ffd9231d811e8b34213f22ab0b0ddafff7749a40243a901c310776e09d2e529806d4d6f0655178953c16707519c3c19b9aaa0d09fb676a9d23525c8bc388053bfccfbc368e3eb04")
    cavp_no_reseed_test(COUNT, EntropyInput, Nonce, PersonalizationString, AdditionalInput0, AdditionalInput1, ReturnedBitsLen, ReturnedBits)

    COUNT = 2
    EntropyInput = bytes.fromhex("9f76503e84727297bc7056c7af917a1c98baa725295457db4fcf54ed09af7f15")
    Nonce = bytes.fromhex("f39c46142b85a67b4b323594b7e97bde")
    PersonalizationString = bytes.fromhex("")
    AdditionalInput0 = bytes.fromhex("")
    AdditionalInput1 = bytes.fromhex("")
    ReturnedBits = bytes.fromhex("7d6a8bc5a7f057ceed6109bfac2486f80f81373b6b31d062aa1fad6d9eda5874867b9ef007ba5a92ba8f3fca624bfd9f7ee5770bbeb0391394fef783c16a7f003c06e5469bab03445bb28a2111def415d162e40472d3e5ae628c5c63170bb19f741c79a5331c883c12bca429f518bf71b14683a071b6c6e1e55d8c7a0f3942bc12a103556c49ca173e498b3b4a15027145cdaeb195bc8a7e1aa82ebdf6ecd516481a4d21f400d0d71b5894545888fee8beed80d3251647947f5abc4735b47fd0")
    cavp_no_reseed_test(COUNT, EntropyInput, Nonce, PersonalizationString, AdditionalInput0, AdditionalInput1, ReturnedBitsLen, ReturnedBits)

    COUNT = 3
    EntropyInput = bytes.fromhex("e242e5b3b49d87289fe02840dc742a2a6cd9490fe2cce581833dddb1edc0d103")
    Nonce = bytes.fromhex("f987f5de5c68cd345c81b032ea55f36d")
    PersonalizationString = bytes.fromhex("")
    AdditionalInput0 = bytes.fromhex("")
    AdditionalInput1 = bytes.fromhex("")
    ReturnedBits = bytes.fromhex("3a858345dfaf00defdf6c83114b760ef53b131fbf14bcc4052cd948820eee78a11cbbd8f4baa308e1d187fced74cbf019c1080d9efffd93fda07df051433876d9900c1f9ad36ea1cb04989bb0c55fd6d01e46923f3bc8887ac00ebd4710212114165355361e240b04232df55a81add3fb363f0d4c9c5e3d313bc7caac7d49dca8517cedacf571fde9686ae93d901fb9b17097a638bb9899cfab0ebc9d1f8a43c2eed7c9f326a711d0f5b9cfc5166c9b561824cbd7775ec601ca712b3ddaaa05b")
    cavp_no_reseed_test(COUNT, EntropyInput, Nonce, PersonalizationString, AdditionalInput0, AdditionalInput1, ReturnedBitsLen, ReturnedBits)

    COUNT = 4
    EntropyInput = bytes.fromhex("42cc17365f5ea5fd22bdc4ade715e293064d6794d82bed5b77c4c107a73de1f7")
    Nonce = bytes.fromhex("6d759e4b191ba01e0ed5dea788ab018d")
    PersonalizationString = bytes.fromhex("")
    AdditionalInput0 = bytes.fromhex("")
    AdditionalInput1 = bytes.fromhex("")
    ReturnedBits = bytes.fromhex("de06dee8c8fe453aa03ac2546c39f5cda12412864d52ed5cbd0d4905dd226746d50d1af9fd3e1d90de0f16295cb7f6f4d3271ef00564709df4b05eb9f8adc0f8e8522b05b9f32c37d8526813898b9f71db57fc8328e3b79144482e8aa55c83934d6e097e43ec6d0bc32edaf8c0e6ca449b2e8388b32b286e2d4f85266b0605fb99d1a647565c95ff7857bcab73662b7218719189d792514edca2b1d0cdcd9b6347e132ef4c323da24ad5afd5ed6f96d27b0f879288e962fa0baca3d5b72b5c70")
    cavp_no_reseed_test(COUNT, EntropyInput, Nonce, PersonalizationString, AdditionalInput0, AdditionalInput1, ReturnedBitsLen, ReturnedBits)

    COUNT = 5
    EntropyInput = bytes.fromhex("d57024a230b825b241c206f7b55e2114461ecc9b75353f12ac1d9ad7e7871481")
    Nonce = bytes.fromhex("fe401c320f74afdb07f566ea500b0628")
    PersonalizationString = bytes.fromhex("")
    AdditionalInput0 = bytes.fromhex("")
    AdditionalInput1 = bytes.fromhex("")
    ReturnedBits = bytes.fromhex("e8930bd55a0a5a6d83a9b3b2cde7085c2ae467ea4a2e65ca303697d492ca878bcb801769eb1b7ec564586ec8b36d350e192c4fbf03a98be0ddecf56d465914ba353ed7734d19a680fc4593d9234c4ac8c23b7dfa1e26b013f590cca43b9fef126121b4842496b11dea3ef5e981cb357341f03f92a546a62609236ded6f7d814456acc0596d555cbdc02cbd47dae2caa1897831ea464225922c6600a8bb92e711653067f83b21e1df054309858948c11a1399736fc8391c5b0fc35629abfa5650")
    cavp_no_reseed_test(COUNT, EntropyInput, Nonce, PersonalizationString, AdditionalInput0, AdditionalInput1, ReturnedBitsLen, ReturnedBits)

    COUNT = 6
    EntropyInput = bytes.fromhex("059ded79125b2d56d9d52bcc950bf608d1a2373515dafcc81efb6588005a5722")
    Nonce = bytes.fromhex("d8f5f4181f9f2a316c93fdfbadf50e75")
    PersonalizationString = bytes.fromhex("")
    AdditionalInput0 = bytes.fromhex("")
    AdditionalInput1 = bytes.fromhex("")
    ReturnedBits = bytes.fromhex("db65d2000632c3d7009c227e99c210e5897f4d7edae608a242b5a4f17708613f8c19a4dd65d6bc3ca57737c9bfdcca068288eea49440af768d1fc977c32b065bb71aa3d8c4d77c9e8e8a6166f332a247978a6c41ed253a1b68ad934a3416b40344a681de28638f00b0a0ffb75514c3f62253372f809906043de35e4805b8e962e5eb957f04212835f802b2c0b3e76c7cf239c89adf31909cd6224d542d929f9b20a10ab99a7c631e4e6188fe2ba8f552c9c88fdadb528679fe950431641b8f37")
    cavp_no_reseed_test(COUNT, EntropyInput, Nonce, PersonalizationString, AdditionalInput0, AdditionalInput1, ReturnedBitsLen, ReturnedBits)

    COUNT = 7
    EntropyInput = bytes.fromhex("4630406b475b1263b6078e93e5d4282205958d94eb97d1e66b429fb69ec9fccd")
    Nonce = bytes.fromhex("0dd9982c338df935e929c42fab66adaf")
    PersonalizationString = bytes.fromhex("")
    AdditionalInput0 = bytes.fromhex("")
    AdditionalInput1 = bytes.fromhex("")
    ReturnedBits = bytes.fromhex("5d80ec072f550981bcaac6787c0488cc470406249ec80f4bf11050630227f8b5ac6b3b369db237d7c24a0980dffe8d3abd9b64fd4efa492349bd4eb6902edb94553546110227d7de5a864ddae8b9fed8de9f0df9c596e39de903fda323ee6f788831452eb9e49c5eef3e058b5bf84f61f735a93e042bb9e458df6b25f42a6eb8fb03d437cfab757fab4990c721a757eaa5e9048208abbcce6e52f177b20dcf52f1fa551a92b68bcdb01680855b8f79131266378cd1f0c2a4141c9675f01d1e48")
    cavp_no_reseed_test(COUNT, EntropyInput, Nonce, PersonalizationString, AdditionalInput0, AdditionalInput1, ReturnedBitsLen, ReturnedBits)

    COUNT = 8
    EntropyInput = bytes.fromhex("6ea9c6f784f12a9707ceac8a7162ee5381dc893ee139f8f4b4d93db266829db4")
    Nonce =  bytes.fromhex("ae92bc52ff860d8ecdc9fc16bd070130")
    PersonalizationString = bytes.fromhex("")
    AdditionalInput0 = bytes.fromhex("")
    AdditionalInput1 = bytes.fromhex("")
    ReturnedBits = bytes.fromhex("234366f1591cfe244956f9496cdf446e0d390ba64beaa066945b1b4c5337dded2619dd2bd0133a5d612bab7c251ab79e3951cb134894c422553fc8cc7b3ccb29c20adbf52dda35af779142d7efc735342db2ee067649fda25f3e8a74f8e4f6620cf5a17cb943602609cafb85bdf482873efa4c74928cc0d69444b72aa6bc72694a3a21c6a721aa4e0fccab0a98aef375a37a3e8a15dccad13b6d70b3483581004642d879804aa00cba207b51affca43490bb98f67953265574366ec3829e67aa")
    cavp_no_reseed_test(COUNT, EntropyInput, Nonce, PersonalizationString, AdditionalInput0, AdditionalInput1, ReturnedBitsLen, ReturnedBits)

    COUNT = 9
    EntropyInput = bytes.fromhex("5c13056be92a7f71236fcfef460298acc8595dd474310727f5ccb9a7acb2254a")
    Nonce = bytes.fromhex("c7226f86349e20e2aca737068ab0f2ce")
    PersonalizationString = bytes.fromhex("")
    AdditionalInput0 = bytes.fromhex("")
    AdditionalInput1 = bytes.fromhex("")
    ReturnedBits = bytes.fromhex("16d415eddefa4dc295a64adcbbcb8c6fe8c8f123c6b09dc08a56d723cff5978cc120fd0a68a2f4c202c220db372d3128ef52385d5786c12dfc6e60ecfc3461a09fa80453e2b1b6365eaeb4df602d192aacb25ab6b4a59689d4bf8d1c4c42a32779f62b06baca6461f154cf40901f5787c1aa2bf67cbfe7546ef5b2bdff20790d8c72d077d48c59c92d1af90a90ccfcdf643dd9d6cee0b1faf5f2f35cfd01d2077ced5e2d013ec1e09336dfab9d9e51ba9a3a2837306213bca2d79abf8dc3282c")
    cavp_no_reseed_test(COUNT, EntropyInput, Nonce, PersonalizationString, AdditionalInput0, AdditionalInput1, ReturnedBitsLen, ReturnedBits)

    COUNT = 10
    EntropyInput = bytes.fromhex("38f08a099fc2d405c32d1e0f867e5450d5ee0d53783c31de9ddeae46d962999d")
    Nonce = bytes.fromhex("a01f13a43320c715612cedb920cf12eb")
    PersonalizationString = bytes.fromhex("")
    AdditionalInput0 = bytes.fromhex("")
    AdditionalInput1 = bytes.fromhex("")
    ReturnedBits = bytes.fromhex("079ce7a5b540cae96c2883e95acde3039048a6c45a2d259cc648639e7205392d91fa3ee080e615f1e0741a0e536c9e05844651b93461bfc547fb452fec61f853e1bd6e08eabd0cf1c5f84f85eca9d42b53d1e5bae51be5fd35189e4f1c02b843c6361fccf4ca6648bf30a23ccb8ebc16fcf158746eb39cd96f19d46707c001e11c4e0e8ccbc89fec66c69fc92843b6bb2ee1cc7595b65ba89ccaccd6130a8417faf705e8e203e90ee64ae970c409389b5cd0ca80a4e40b642689741691b20621")
    cavp_no_reseed_test(COUNT, EntropyInput, Nonce, PersonalizationString, AdditionalInput0, AdditionalInput1, ReturnedBitsLen, ReturnedBits)

    COUNT = 11
    EntropyInput = bytes.fromhex("0863c868c32442a1a64095a71ab6ae2f9e61c119b58dfa4f34efd26593bbbf68")
    Nonce = bytes.fromhex("bc407904c43300452dd4e61df47fa98f")
    PersonalizationString = bytes.fromhex("")
    AdditionalInput0 = bytes.fromhex("")
    AdditionalInput1 = bytes.fromhex("")
    ReturnedBits = bytes.fromhex("585334828cf531828fc7127fee0c926f85b8e71e8522ea921296dc62b83a09a00397cd45e0664d0f26fa24edd3e3d8ecef8fdd77ab22431d4066f0efaf3882c97f179a7060efe9e8cba5d8145bebd502c0e09ee791231d539983c08860d7783edb58440d193ed82bc77c27723381a0da45bb1fc2a609f8b73b90446e39869a5af5038aff603b44db9771113927a5297fdc3450eaa228e313afe43c31b0a95b476c5ca312b4f589f809749481722cea9990c02b647976aa6c6f02ce1e5e6ea6df")
    cavp_no_reseed_test(COUNT, EntropyInput, Nonce, PersonalizationString, AdditionalInput0, AdditionalInput1, ReturnedBitsLen, ReturnedBits)

    COUNT = 12
    EntropyInput = bytes.fromhex("a41ad223e41e2bb9c131ec945ca310600ab00c51f6e4fcddd803bd9ab9be8af5")
    Nonce = bytes.fromhex("483373838894d32745a81ba9d6967751")
    PersonalizationString = bytes.fromhex("")
    AdditionalInput0 = bytes.fromhex("")
    AdditionalInput1 = bytes.fromhex("")
    ReturnedBits = bytes.fromhex("95ca31a7eeebdd2348cf1d43411d2c35faffdbcaed4052d50cf92f0e9d2e757686b72d631a56ca98b68215e7014cfed943abc1e13441c1d660f13adf2188d0975154e1b42a592a62a43b57f82cc21a428873a92fda83abe420efb5233140e4d6c7852cf81e85961fa5c606c5f33e06077f414b0f814cbbe50cc606bffbd474364e608825fdaaf5e74d862795539be8697e2ce05d71446881e3f65bb54ed95e941586988f6e0c34e1beef426696e9dbd9a214013d826a8c99a2a686d8402c583f")
    cavp_no_reseed_test(COUNT, EntropyInput, Nonce, PersonalizationString, AdditionalInput0, AdditionalInput1, ReturnedBitsLen, ReturnedBits)

    COUNT = 13
    EntropyInput = bytes.fromhex("62a26c1327c0ebf8b40691fb4c8f812e81f5474b0c7db70aa9424110fee3a05e")
    Nonce = bytes.fromhex("41c0cf2e87210e34d0c6bffc269bf2ba")
    PersonalizationString = bytes.fromhex("")
    AdditionalInput0 = bytes.fromhex("")
    AdditionalInput1 = bytes.fromhex("")
    ReturnedBits = bytes.fromhex("6e20a00df1af37e6cc55e580ba21335111eb375395343618df7d630b9dc234496e3964cd45c5de34bda46a28964f6148704c30925feeaecae0574038434cd33c1dd943207a8dbdcd72dc9ecb76a25728b3c2a8ac13c1de3a126d7d43a46e12e0d0ca8991469e582b78ef6aa691b5a0e3e85cba7d7aea3c1e8e031674e85f5af36546eb2a0a28d4ffbaa316a9a6c944fce291cc0c235e8499882eb62b22b548ae07cf9430329e009f4443cb94f7a14e8661166b0d681dcec867205abed48145e9")
    cavp_no_reseed_test(COUNT, EntropyInput, Nonce, PersonalizationString, AdditionalInput0, AdditionalInput1, ReturnedBitsLen, ReturnedBits)

    COUNT = 14
    EntropyInput = bytes.fromhex("fd54cf77ed35022a3fd0dec88e58a207c8c069250066481388f12841d38ad985")
    Nonce = bytes.fromhex("91f9c02a1d205cdbcdf4d93054fde5f5")
    PersonalizationString = bytes.fromhex("")
    AdditionalInput0 = bytes.fromhex("")
    AdditionalInput1 = bytes.fromhex("")
    ReturnedBits = bytes.fromhex("f6d5bf594f44a1c7c9954ae498fe993f67f4e67ef4e349509719b7fd597311f2c123889203d90f147a242cfa863c691dc74cfe7027de25860c67d8ecd06bcd22dfec34f6b6c838e5aab34d89624378fb5598b9f30add2e10bdc439dcb1535878cec90a7cf7251675ccfb9ee37932b1a07cd9b523c07eff45a5e14d888be830c5ab06dcd5032278bf9627ff20dbec322e84038bac3b46229425e954283c4e061383ffe9b0558c59b1ece2a167a4ee27dd59afeeb16b38fbdb3c415f34b1c83a75")
    cavp_no_reseed_test(COUNT, EntropyInput, Nonce, PersonalizationString, AdditionalInput0, AdditionalInput1, ReturnedBitsLen, ReturnedBits)

    COUNT = 15
    EntropyInput = bytes.fromhex("5e919d353357671566d2c6ab6e1acd46f47d0c878fe36114d7fea9fecb88a3a2")
    Nonce = bytes.fromhex("7efca9e3d1e1b09d7f16832f3af75141")
    PersonalizationString = bytes.fromhex("")
    AdditionalInput0 = bytes.fromhex("442f17cb3cb1482a19729bfd58f46f6ef16285554892c01b0718968d6e011082")
    AdditionalInput1 = bytes.fromhex("f9557c93eb841bfd7b5d4b71da928efcbe3f55e1870493ef90d16eb238380d65")
    ReturnedBits = bytes.fromhex("36902134f1989cfe7eb518a56c06aada98997d9bacd04aee21f879a57b515ca3b5e0c2d5fed05ca1a8b054e8c46b389d9d9186feb0abe8e2e60b3a267281cc5b4b7341116ced35a0e07bc2b0330bbfd8b07f07248fa6d8fc5c9df13445324162bdfa22a91ba71453ab123c92f91c70b8bd540b3b180b11ab45ae2c59e57c7c43dab7576594959a96eb502d182267c86576b1846ccee1a694cabdfb42e0c8214192efb502926fa3c27eed020b7cc8866a5af9d838a57e78bf7acd230e1f4d8361")
    cavp_no_reseed_test(COUNT, EntropyInput, Nonce, PersonalizationString, AdditionalInput0, AdditionalInput1, ReturnedBitsLen, ReturnedBits)

def caliptra_test_vectors():
    COUNT = 0
    entropy = bytes.fromhex("000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000")
    nonce = bytes.fromhex("000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000")
    expected0 = bytes.fromhex("FEEEF5544A76564990128AD189E873F21F0DFD5AD7E2FA861127EE6E394CA784871C1AEC032C7A8B10B93E0EAB8946D6")
    expected1 = bytes.fromhex("d7f1b8ee5fc4eca7b022ccbdc2b03bee146c8985ea52ae400b9e23ce3cb3a95849ef93140c8a519ed8f817e66e6f0de4")
    caliptra_test(COUNT, entropy, nonce, expected0, expected1)

    COUNT = 1
    entropy = bytes.fromhex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF")
    nonce = bytes.fromhex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF")
    expected0 = bytes.fromhex("7F68A6D896EA5DA62E78DEDB46F6662BC141F2F0B9E641ACC7342663FD51444E380FEA1DABBCA55F18987C0CFC10DF77")
    expected1 = bytes.fromhex("b52178b3c26aeff4a9f2704664c091d8cf57b45d05c2bb8c7bfcf56963fbe7674908ae830bfe10e0de2eccf48fa7b050")
    caliptra_test(COUNT, entropy, nonce, expected0, expected1)

    COUNT = 2
    entropy = bytes.fromhex("F71EE80F1D123DC3F70EAA1FB3272714858EA555BC496BF39ADB107B192BF0BCBA9BB5B5799CFF8E12A1154F37CA7BBD")
    nonce = bytes.fromhex("DE2B2A66EE13797C69438A9BF6F8514C0A8ABEFD3E5533E1119AE88E8D641771E9BCE4CBE44430A0ADAAAB4103095FC4")
    expected0 = bytes.fromhex("316f0937ff54b3d16398d5d07799ab59d0e1f3962831101f1eca892f0f1567df2f964c19b8690761d188d2100403eea6")
    expected1 = bytes.fromhex("9a42b5046712b4e32c1f9db62a7900d2e0d4e051580b5dc2cbc8498a04df6676ff80b4e6e2b34b29152bd96e5b4eefed")
    expected2 = bytes.fromhex("28ff268d4fea88d4bc28a712feb777bb72dace10e9886eefd226615f5f9d508aa8f59d4b087b65d54223a2186f53031b")
    caliptra_test(COUNT, entropy, nonce, expected0, expected1, expected2)


if __name__ == "__main__":
#    cavp_test_vectors()
   caliptra_test_vectors()