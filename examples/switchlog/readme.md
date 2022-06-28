#### switchlog example applications

This directory contains the switchlog example applications. Each subdirectory contains: the example application, a P4 harness program, and an event parser configuration file, which links the p4 harness to the program. 

##### Compiling to P4 and measuring Tofino resource usage

1. run `./compile.py compile_cmds.json` to compile the programs to p4, then to Tofino.
2. run `./report_stats.py __testbuilds` to print summaries of resource utilization for the compiles programs.