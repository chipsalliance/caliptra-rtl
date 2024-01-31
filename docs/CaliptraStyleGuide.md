
_*Last Update: 2024/01/31*_

* Consistent reset names: cptra\_rst\_b, cptra\_noncore\_rst\_b, cptra\_uc\_rst\_b, cptra\_pwrgood
* case inside
* FSM conventions:
  three-always-block
  arc\_stuff
  fsm_*_ps
* top module vs lower level naming convention
* Interrupt registers
* interfaces, structs, ports
* suffixes
  \_ps, \_ns: states, present/next
  \_r, \_d, \_p: registered, delayed, pulse
  \_e, \_s, \_t: enum, struct, typedef
  \_i/\_o: input, output
  \_q/\_nq: qualified, non-qualified
  \_b, \_n, \_l: bar/not,negative/low(active)
* assign vs. always\_comb
* always\_latch
* if-else + multi-signal assignment in a single always block
* signal naming convention
  - CamelCase: 
  - pascalCase:
  - snake\_case: signal, port names
  - UPPER\_SNAKE\_CASE: Parameters, localparams, defines
