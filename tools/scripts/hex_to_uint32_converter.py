#!/usr/bin/env python3
"""
Hex to uint32_t Array Converter for AES Test Vectors
Converts hex strings to little endian uint32_t arrays for C code
"""

def hex_to_uint32_compound_literal(hex_str, pad_to_dwords=None):
    """Convert hex string to uint32_t compound literal in little endian format"""
    if not hex_str:
        return "(uint32_t[]){} /* Empty array */"
    
    # Remove any whitespace and ensure even length
    hex_str = hex_str.replace(" ", "").replace("\n", "")
    if len(hex_str) % 2 != 0:
        hex_str = "0" + hex_str
    
    # Pad to specific number of dwords if requested (for IV padding)
    if pad_to_dwords is not None:
        target_hex_chars = pad_to_dwords * 8  # 8 hex chars per dword
        if len(hex_str) < target_hex_chars:
            hex_str = hex_str + "0" * (target_hex_chars - len(hex_str))
    
    # Convert to bytes
    bytes_data = bytes.fromhex(hex_str)
    
    # Pad to multiple of 4 bytes if necessary (if not already padded above)
    while len(bytes_data) % 4 != 0:
        bytes_data += b'\x00'
    
    # Convert to uint32_t array (little endian)
    uint32_array = []
    for i in range(0, len(bytes_data), 4):
        # Little endian: LSB first
        value = (bytes_data[i] | 
                (bytes_data[i+1] << 8) | 
                (bytes_data[i+2] << 16) | 
                (bytes_data[i+3] << 24))
        uint32_array.append(f"0x{value:08x}")
    
    # Format as compound literal
    array_elements = ", ".join(uint32_array)
    return f"(uint32_t[]){{{array_elements}}}"

def convert_single_test_vector(plaintext, ciphertext, tag, aad, iv, key, test_name):
    """Convert a single test vector for easy copy-paste into existing C code"""
    length_dwords = len(plaintext) // 8  # 8 hex chars = 4 bytes = 1 dword
    
    print(f"    {{ // {test_name}")
    print(f"        .plaintext = {hex_to_uint32_compound_literal(plaintext)},")
    print(f"        .ciphertext = {hex_to_uint32_compound_literal(ciphertext)},")
    print(f"        .tag = {hex_to_uint32_compound_literal(tag)},")
    print(f"        .aad = {hex_to_uint32_compound_literal(aad)},")
    print(f"        .iv = {hex_to_uint32_compound_literal(iv, pad_to_dwords=4)},  // Padded to 4 dwords")
    print(f"        .key = {hex_to_uint32_compound_literal(key)},")
    print(f"        .length_dwords = {length_dwords}")
    print("    },")
    print()

def convert_test_vector_to_struct(plaintext, ciphertext, tag, aad, iv, key, test_name):
    """Convert a complete test vector to C structure format"""
    length_dwords = len(plaintext) // 8  # 8 hex chars = 4 bytes = 1 dword
    key_dwords = len(key) // 8  # Calculate key length in dwords
    aad_dwords = len(aad) // 8  # Calculate AAD length in dwords
    
    print(f"    {{ // {test_name}")
    print(f"        .plaintext = {hex_to_uint32_compound_literal(plaintext)},")
    print(f"        .ciphertext = {hex_to_uint32_compound_literal(ciphertext)},")
    print(f"        .tag = {hex_to_uint32_compound_literal(tag)},")
    print(f"        .aad = {hex_to_uint32_compound_literal(aad)},")
    print(f"        .iv = {hex_to_uint32_compound_literal(iv, pad_to_dwords=4)},  // Padded to 4 dwords")
    print(f"        .key = {hex_to_uint32_compound_literal(key)},")
    print(f"        .length_dwords = {length_dwords},")
    print(f"        .key_dwords = {key_dwords},    // Key length in dwords")
    print(f"        .aad_dwords = {aad_dwords}     // AAD length in dwords")
    print("    },")

def main():
    # Test vectors from your code
    test_vectors = [
        {
            "plaintext": "d9313225",
            "ciphertext": "522dc1f0", 
            "tag": "43aa82ef9cebd0dc5b2f4808c58175b0",
            "aad": "feedfacedeadbeeffeedfacedeadbeefabaddad2",
            "iv": "cafebabefacedbaddecaf888",
            "key": "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
            "name": "1 DWORD (4 bytes)"
        },
        {
            "plaintext": "d9313225f88406e5",
            "ciphertext": "522dc1f099567d07",
            "tag": "414ec2648b29e3dbc203cd1adce7da60", 
            "aad": "feedfacedeadbeeffeedfacedeadbeefabaddad2",
            "iv": "cafebabefacedbaddecaf888",
            "key": "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
            "name": "2 DWORDS (8 bytes)"
        },
        {
            "plaintext": "d9313225f88406e5a55909c5",
            "ciphertext": "522dc1f099567d07f47f37a3",
            "tag": "8fbaf6b15ba13f32fde8b82ff6427714",
            "aad": "feedfacedeadbeeffeedfacedeadbeefabaddad2", 
            "iv": "cafebabefacedbaddecaf888",
            "key": "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
            "name": "3 DWORDS (12 bytes)"
        },
        {
            "plaintext": "d9313225f88406e5a55909c5aff5269a",
            "ciphertext": "522dc1f099567d07f47f37a32a84427d",
            "tag": "5b1cf91b45c59ca2e025e6bec8b6a6ea",
            "aad": "feedfacedeadbeeffeedfacedeadbeefabaddad2",
            "iv": "cafebabefacedbaddecaf888", 
            "key": "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
            "name": "4 DWORDS (16 bytes)"
        },
        {
            "plaintext": "d9313225f88406e5a55909c5aff5269a86a7a953",
            "ciphertext": "522dc1f099567d07f47f37a32a84427d643a8cdc",
            "tag": "10501bc85651ae8f4176d6c5a5ea9f3f",
            "aad": "feedfacedeadbeeffeedfacedeadbeefabaddad2",
            "iv": "cafebabefacedbaddecaf888",
            "key": "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
            "name": "5 DWORDS (20 bytes)"
        },
        {
            "plaintext": "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da",
            "ciphertext": "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c9",
            "tag": "1dcc2e8303bec917f99e1b00c24a2dd5",
            "aad": "feedfacedeadbeeffeedfacedeadbeefabaddad2",
            "iv": "cafebabefacedbaddecaf888",
            "key": "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
            "name": "6 DWORDS (24 bytes)"
        },
        {
            "plaintext": "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d",
            "ciphertext": "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd",
            "tag": "eb6c818e5672c8aa6a37889be741d2ca",
            "aad": "feedfacedeadbeeffeedfacedeadbeefabaddad2",
            "iv": "cafebabefacedbaddecaf888",
            "key": "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
            "name": "7 DWORDS (28 bytes)"
        },
        {
            "plaintext": "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a72",
            "ciphertext": "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa",
            "tag": "cf9bffa9bd334d8240c868342b36b506",
            "aad": "feedfacedeadbeeffeedfacedeadbeefabaddad2",
            "iv": "cafebabefacedbaddecaf888",
            "key": "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
            "name": "8 DWORDS (32 bytes)"
        },
        {
            "plaintext": "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a72d95153e5",
            "ciphertext": "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa49ddd138",
            "tag": "9d069e38c0e3290667ad1382bd35f2a1",
            "aad": "feedfacedeadbeeffeedfacedeadbeefabaddad2",
            "iv": "cafebabefacedbaddecaf888",
            "key": "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
            "name": "9 DWORDS (36 bytes)"
        },
        {
            "plaintext": "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a72d95153e52395fec8",
            "ciphertext": "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa49ddd138eff04ca6",
            "tag": "fcfd895f3cfa4618d6b42639182e2634",
            "aad": "feedfacedeadbeeffeedfacedeadbeefabaddad2",
            "iv": "cafebabefacedbaddecaf888",
            "key": "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
            "name": "10 DWORDS (40 bytes)"
        },
        {
            "plaintext": "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a72d95153e52395fec890543def",
            "ciphertext": "522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa49ddd138eff04ca6182bb8db",
            "tag": "d16fcc300228a742e4699bfff43a22ab",
            "aad": "feedfacedeadbeeffeedfacedeadbeefabaddad2",
            "iv": "cafebabefacedbaddecaf888",
            "key": "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
            "name": "11 DWORDS (44 bytes)"
        },
        {
            "plaintext": "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a72d95153e52395fec890543defa3485762",
            "ciphertext":"522dc1f099567d07f47f37a32a84427d643a8cdcbfe5c0c97598a2bd2555d1aa49ddd138eff04ca6182bb8dbbc6c6a7f",
            "tag": "0f7b218f5d52ef7d4997aa56af7ded16",
            "aad": "feedfacedeadbeeffeedfacedeadbeefabaddad2",
            "iv": "cafebabefacedbaddecaf888",
            "key": "feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308",
            "name": "12 DWORDS (48 bytes)"
        }
    ]
    
    print("// Auto-generated aes_gcm_vectors_t structure initialization")
    print("// Generated in little endian format for compound literals")
    print("static const aes_gcm_vectors_t gcm_test_vectors[] = {")
    print("    // AES-256 key: feffe9928665731c6d6a8f9467308308feffe9928665731c6d6a8f9467308308")
    print("    // IV (96-bit): cafebabefacedbaddecaf888") 
    print("    // AAD: feedfacedeadbeeffeedfacedeadbeefabaddad2")
    print()
    print()
    
    for vector in test_vectors:
        convert_test_vector_to_struct(
            vector["plaintext"],
            vector["ciphertext"], 
            vector["tag"],
            vector["aad"],
            vector["iv"],
            vector["key"],
            vector["name"]
        )
    
    print("};")
    print()
    print(f"// Total test vectors: {len(test_vectors)}")

if __name__ == "__main__":
    main()
