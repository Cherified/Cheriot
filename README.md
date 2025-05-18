# Cheriot
CHERIoT implementation in Guru

The Makefile expects [CHERIoT RTOS](https://github.com/CHERIoT-Platform/cheriot-rtos) installed in ${CHERIOT_ROOT}/cheriot-rtos and [CHERIoT LLVM](https://github.com/CHERIoT-Platform/llvm-project) in ${CHERIOT_ROOT}/cheriot-llvm.
Use this [link](https://github.com/CHERIoT-Platform/cheriot-rtos/blob/main/docs/GettingStarted.md#building-cheriot-llvm) to build LLVM.
The object that is being initialized in the Switcher array is the entry.S file from CHERIoT's switcher, which can be obtained using

`${CHERIOT_ROOT}/cheriot-llvm/builds/cheriot-llvm/bin/llvm-objdump -d ${CHERIOT_ROOT}/cheriot-rtos/examples/02.hello_compartment/build/.objs/cheriot.switcher/cheriot/cheriot/release/__/__/sdk/core/switcher/entry.S.o`
