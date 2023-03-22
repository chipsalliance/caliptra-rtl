GCC_PREFIX    ?= riscv64-unknown-elf
MAKEFILE_PATH  = $(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))
PICOLIBC_PATH  = $(abspath $(MAKEFILE_PATH)/../../../../../third_party/picolibc)
BUILD_PATH     = $(PICOLIBC_PATH)/build

ifeq ($(CCACHE), )
	MESON_CROSS_CC = '$(GCC_PREFIX)-gcc'
else
	MESON_CROSS_CC = ['$(CCACHE)', '$(GCC_PREFIX)-gcc']
endif

define CROSSFILE
[binaries]
c     = $(MESON_CROSS_CC)
ar    = '$(GCC_PREFIX)-gcc-ar'
as    = '$(GCC_PREFIX)-as'
nm    = '$(GCC_PREFIX)-gcc-nm'
strip = '$(GCC_PREFIX)-strip'

[host_machine]
system     = 'unknown'
cpu_family = 'riscv'
cpu        = 'riscv'
endian     = 'little'

[built-in options]
c_args      = [ $(foreach flag,$(filter-out $(DEPFLAGS) -flto,$(CFLAGS)),'$(flag)',) ]
c_link_args = [ $(foreach flag,$(filter-out -flto,$(LDFLAGS)),'$(flag)',) ]
endef

export CROSSFILE

$(BUILD_PATH):
	mkdir -p $@

$(BUILD_PATH)/cross.txt: | $(BUILD_PATH)
	@echo "$$CROSSFILE" > $@

$(BUILD_PATH)/libc.a: $(BUILD_PATH)/cross.txt | $(BUILD_PATH)

	cd $(PICOLIBC_PATH) && meson $(BUILD_PATH) \
		-Dmultilib=false \
		-Dpicocrt=false \
		-Datomic-ungetc=false \
		-Dthread-local-storage=false \
		-Dio-long-long=true \
		-Dformat-default=integer \
		-Dincludedir=picolibc/$(GCC_PREFIX)/include \
		-Dlibdir=picolibc/$(GCC_PREFIX)/lib \
		--cross-file $(BUILD_PATH)/cross.txt

	cd $(BUILD_PATH) && meson compile
	cp $(BUILD_PATH)/newlib/libc.a $@

all: $(BUILD_PATH)/libc.a | $(BUILD_PATH)

.PHONY: all
