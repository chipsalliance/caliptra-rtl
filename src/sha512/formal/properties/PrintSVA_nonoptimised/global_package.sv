// -------------------------------------------------
// Copyright(c) LUBIS EDA GmbH, All rights reserved
// Created on 15.06.2023 at 15:24
// Contact: contact@lubis-eda.com
// Author: Tobias Ludwig, Michael Schwarz
// -------------------------------------------------


package global_package;


// Functions

function bit unsigned [63:0] Ch(bit unsigned [63:0] a, bit unsigned [63:0] b, bit unsigned [63:0] c);
  return ((a & b) ^ (~a & c));
endfunction

function bit unsigned [63:0] Maj(bit unsigned [63:0] x, bit unsigned [63:0] y, bit unsigned [63:0] z);
  return (((x & y) ^ (x & z)) ^ (y & z));
endfunction

function bit unsigned [63:0] T1(bit unsigned [63:0] e, bit unsigned [63:0] f, bit unsigned [63:0] g, bit unsigned [63:0] h, bit unsigned [63:0] k, bit unsigned [63:0] w);
  return 64'(((((h + sigma1(e)) + Ch(e, f, g)) + k) + w));
endfunction

function bit unsigned [63:0] T2(bit unsigned [63:0] a, bit unsigned [63:0] b, bit unsigned [63:0] c);
  return 64'((sigma0(a) + Maj(a, b, c)));
endfunction

function bit unsigned [63:0] delta0(bit unsigned [63:0] x);
  return ((rotr1(x) ^ rotr8(x)) ^ shr7(x));
endfunction

function bit unsigned [63:0] delta1(bit unsigned [63:0] x);
  return ((rotr19(x) ^ rotr61(x)) ^ shr6(x));
endfunction

function bit unsigned [63:0] rotr1(bit unsigned [63:0] n);
  return 64'(((n >> 64'd1) | (n << 64'd63)));
endfunction

function bit unsigned [63:0] rotr14(bit unsigned [63:0] n);
  return 64'(((n >> 64'd14) | (n << 64'd50)));
endfunction

function bit unsigned [63:0] rotr18(bit unsigned [63:0] n);
  return 64'(((n >> 64'd18) | (n << 64'd46)));
endfunction

function bit unsigned [63:0] rotr19(bit unsigned [63:0] n);
  return 64'(((n >> 64'd19) | (n << 64'd45)));
endfunction

function bit unsigned [63:0] rotr28(bit unsigned [63:0] n);
  return 64'(((n >> 64'd28) | (n << 64'd36)));
endfunction

function bit unsigned [63:0] rotr34(bit unsigned [63:0] n);
  return 64'(((n >> 64'd34) | (n << 64'd30)));
endfunction

function bit unsigned [63:0] rotr39(bit unsigned [63:0] n);
  return 64'(((n >> 64'd39) | (n << 64'd25)));
endfunction

function bit unsigned [63:0] rotr41(bit unsigned [63:0] n);
  return 64'(((n >> 64'd41) | (n << 64'd23)));
endfunction

function bit unsigned [63:0] rotr61(bit unsigned [63:0] n);
  return 64'(((n >> 64'd61) | (n << 64'd3)));
endfunction

function bit unsigned [63:0] rotr8(bit unsigned [63:0] n);
  return 64'(((n >> 64'd8) | (n << 64'd56)));
endfunction

function bit unsigned [63:0] shr6(bit unsigned [63:0] n);
  return (n >> 64'd6);
endfunction

function bit unsigned [63:0] shr7(bit unsigned [63:0] n);
  return (n >> 64'd7);
endfunction

function bit unsigned [63:0] sigma0(bit unsigned [63:0] x);
  return ((rotr28(x) ^ rotr34(x)) ^ rotr39(x));
endfunction

function bit unsigned [63:0] sigma1(bit unsigned [63:0] x);
  return ((rotr14(x) ^ rotr18(x)) ^ rotr41(x));
endfunction

function bit unsigned [63:0] slicer(bit unsigned [1023:0] block, bit signed [31:0] index);
  if ((index == 'sd0))
    return 64'((block >> 1024'd0));
  else if ((index == 'sd1))
    return 64'((block >> 1024'd64));
  else if ((index == 'sd2))
    return 64'((block >> 1024'd128));
  else if ((index == 'sd3))
    return 64'((block >> 1024'd192));
  else if ((index == 'sd4))
    return 64'((block >> 1024'd256));
  else if ((index == 'sd5))
    return 64'((block >> 1024'd320));
  else if ((index == 'sd6))
    return 64'((block >> 1024'd384));
  else if ((index == 'sd7))
    return 64'((block >> 1024'd448));
  else if ((index == 'sd8))
    return 64'((block >> 1024'd512));
  else if ((index == 'sd9))
    return 64'((block >> 1024'd576));
  else if ((index == 'sd10))
    return 64'((block >> 1024'd640));
  else if ((index == 'sd11))
    return 64'((block >> 1024'd704));
  else if ((index == 'sd12))
    return 64'((block >> 1024'd768));
  else if ((index == 'sd13))
    return 64'((block >> 1024'd832));
  else if ((index == 'sd14))
    return 64'((block >> 1024'd896));
  else if ((index == 'sd15))
    return 64'((block >> 1024'd960));
  else
    return 64'((block >> 1024'd960));
endfunction


endpackage
