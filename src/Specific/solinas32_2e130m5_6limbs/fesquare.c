static void fesquare(uint32_t out[6], const uint32_t in1[6]) {
  { const uint32_t x9 = in1[5];
  { const uint32_t x10 = in1[4];
  { const uint32_t x8 = in1[3];
  { const uint32_t x6 = in1[2];
  { const uint32_t x4 = in1[1];
  { const uint32_t x2 = in1[0];
  { uint64_t x11 = (((uint64_t)x2 * x9) + (((uint64_t)x4 * x10) + (((uint64_t)x6 * x8) + (((uint64_t)x8 * x6) + (((uint64_t)x10 * x4) + ((uint64_t)x9 * x2))))));
  { uint64_t x12 = ((((uint64_t)x2 * x10) + (((uint64_t)x4 * x8) + ((0x2 * ((uint64_t)x6 * x6)) + (((uint64_t)x8 * x4) + ((uint64_t)x10 * x2))))) + (0x5 * (0x2 * ((uint64_t)x9 * x9))));
  { uint64_t x13 = ((((uint64_t)x2 * x8) + ((0x2 * ((uint64_t)x4 * x6)) + ((0x2 * ((uint64_t)x6 * x4)) + ((uint64_t)x8 * x2)))) + (0x5 * ((0x2 * ((uint64_t)x10 * x9)) + (0x2 * ((uint64_t)x9 * x10)))));
  { uint64_t x14 = ((((uint64_t)x2 * x6) + (((uint64_t)x4 * x4) + ((uint64_t)x6 * x2))) + (0x5 * (((uint64_t)x8 * x9) + (((uint64_t)x10 * x10) + ((uint64_t)x9 * x8)))));
  { uint64_t x15 = ((((uint64_t)x2 * x4) + ((uint64_t)x4 * x2)) + (0x5 * ((0x2 * ((uint64_t)x6 * x9)) + (((uint64_t)x8 * x10) + (((uint64_t)x10 * x8) + (0x2 * ((uint64_t)x9 * x6)))))));
  { uint64_t x16 = (((uint64_t)x2 * x2) + (0x5 * ((0x2 * ((uint64_t)x4 * x9)) + ((0x2 * ((uint64_t)x6 * x10)) + (((uint64_t)x8 * x8) + ((0x2 * ((uint64_t)x10 * x6)) + (0x2 * ((uint64_t)x9 * x4))))))));
  { uint32_t x17 = (uint32_t) (x16 >> 0x16);
  { uint32_t x18 = ((uint32_t)x16 & 0x3fffff);
  { uint64_t x19 = (x17 + x15);
  { uint32_t x20 = (uint32_t) (x19 >> 0x16);
  { uint32_t x21 = ((uint32_t)x19 & 0x3fffff);
  { uint64_t x22 = (x20 + x14);
  { uint32_t x23 = (uint32_t) (x22 >> 0x15);
  { uint32_t x24 = ((uint32_t)x22 & 0x1fffff);
  { uint64_t x25 = (x23 + x13);
  { uint32_t x26 = (uint32_t) (x25 >> 0x16);
  { uint32_t x27 = ((uint32_t)x25 & 0x3fffff);
  { uint64_t x28 = (x26 + x12);
  { uint32_t x29 = (uint32_t) (x28 >> 0x16);
  { uint32_t x30 = ((uint32_t)x28 & 0x3fffff);
  { uint64_t x31 = (x29 + x11);
  { uint32_t x32 = (uint32_t) (x31 >> 0x15);
  { uint32_t x33 = ((uint32_t)x31 & 0x1fffff);
  { uint32_t x34 = (x18 + (0x5 * x32));
  { uint32_t x35 = (x34 >> 0x16);
  { uint32_t x36 = (x34 & 0x3fffff);
  { uint32_t x37 = (x35 + x21);
  { uint32_t x38 = (x37 >> 0x16);
  { uint32_t x39 = (x37 & 0x3fffff);
  out[0] = x36;
  out[1] = x39;
  out[2] = (x38 + x24);
  out[3] = x27;
  out[4] = x30;
  out[5] = x33;
  }}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
}