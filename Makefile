.PHONY: coq clean force haskell

.DEFAULT_GOAL = haskell

CHERIOT_ROOT = $(HOME)/work/Cheriot
CURR_DIR = $(shell pwd)

Switcher.v:
	echo "From Stdlib Require Import List ZArith Zmod." > Switcher.v
	echo "" >> Switcher.v
	echo "Local Open Scope Z_scope." >> Switcher.v
	echo "" >> Switcher.v
	echo "Definition switcher: list (bits 8) := (" >> Switcher.v
	echo $(CURR_DIR)
	cd $(CHERIOT_ROOT)/cheriot-rtos/examples/02.hello_compartment && xmake config --sdk=$(CHERIOT_ROOT)/llvm-project/builds/cheriot-llvm && xmake && cd $(CURR_DIR)
	$(CHERIOT_ROOT)/llvm-project/builds/cheriot-llvm/bin/llvm-objcopy -O binary -j .text $(CHERIOT_ROOT)/cheriot-rtos/examples/02.hello_compartment/build/.objs/cheriot.switcher/cheriot/cheriot/release/__/__/sdk/core/switcher/entry.S.o $(CURR_DIR)/tmp && cd $(CURR_DIR)
	hexdump -e '1/1 "Zmod.of_Z _ 0x%02x " "::\n"' -v tmp >> Switcher.v
	rm tmp
	echo "nil)." >> Switcher.v

coq: Makefile.coq.all Switcher.v
	$(MAKE) -j -C ../Guru
	$(MAKE) -f Makefile.coq.all

Makefile.coq.all: force
	$(COQBIN)rocq makefile -f _CoqProject -o Makefile.coq.all

haskell: coq
	$(MAKE) -C $(CURR_DIR)/../Guru/PrettyPrinter

force:

clean:: Makefile.coq.all
	$(MAKE) -C ../Guru clean
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
	rm -f Switcher.v

