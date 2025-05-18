VS:=$(shell find . -type f -name '*.v')

.PHONY: coq clean force haskell

.DEFAULT_GOAL = coq

CHERIOT_ROOT = $(HOME)/CHERIOT
CURR_DIR = $(shell pwd)

Switcher.v:
	echo "Require Import List BinInt." > Switcher.v
	echo "Import ListNotations." >> Switcher.v
	echo "" >> Switcher.v
	echo "Local Open Scope Z_scope." >> Switcher.v
	echo "" >> Switcher.v
	echo "Definition switcher: list Z := (" >> Switcher.v
	echo $(CURR_DIR)
	cd $(CHERIOT_ROOT)/cheriot-rtos/examples/02.hello_compartment && xmake config --sdk=$(CHERIOT_ROOT)/cheriot-llvm/builds/cheriot-llvm && xmake && cd $(CURR_DIR)
	$(CHERIOT_ROOT)/cheriot-llvm/builds/cheriot-llvm/bin/llvm-objcopy -O binary -j .text $(CHERIOT_ROOT)/cheriot-rtos/examples/02.hello_compartment/build/.objs/cheriot.switcher/cheriot/cheriot/release/__/__/sdk/core/switcher/entry.S.o $(CURR_DIR)/tmp && cd $(CURR_DIR)
	hexdump -e '1/1 "%03u " "::\n"' -v tmp >> Switcher.v
	rm tmp
	echo "nil)." >> Switcher.v

coq: Makefile.coq.all $(VS) Switcher.v
	$(MAKE) -j -C ../Guru
	$(MAKE) -f Makefile.coq.all

Makefile.coq.all: force
	$(COQBIN)coq_makefile -f _CoqProject $(VS) -o Makefile.coq.all

force:

clean:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all clean
	find . -type f -name '*.v.d' -exec rm {} \;
	find . -type f -name '*.glob' -exec rm {} \;
	find . -type f -name '*.vo' -exec rm {} \;
	find . -type f -name '*.vos' -exec rm {} \;
	find . -type f -name '*.vok' -exec rm {} \;
	find . -type f -name '*.~' -exec rm {} \;
	find . -type f -name '*.hi' -exec rm {} \;
	find . -type f -name '*.o' -exec rm {} \;
	find . -type f -name '*.aux' -exec rm {} \;
	rm -f Makefile.coq.all Makefile.coq.all.conf .Makefile.coq.all.d
	rm -f .nia.cache .lia.cache

