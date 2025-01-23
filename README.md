# Turing Machines & Busy Beavers

A little program for playing around with Turing Machines.

## Features
- Calculation of the Turing Machine's number, given its transition table
- Calculation of the Turing Machine's transition table, given its number
- Simulation of Turing Machines (and Busy Beavers number calculation)


### Turing Machines
State space size:  `( =(4(n+1))^(2n) )`

|States|TMs|
|------|---|
|1|1|
|2|64|
|3|20736|
|4|16777216|
|5|25600000000|
|6|63403380965376|
|7| 232218265089212416|
|8|1180591620717411303424|
|9|7958661109946400884391936|
|10|68719476736000000000000000000|
|11|739696442014594807059393047166976|
|12|9711967541295580042210555933809967104|
|13|152784834199652075368661148843397208866816|

### Busy Beavers
|States|TM number|Ones|Transitions|Std format|
|------|---------|----|-----------|----------|
|1|56|1|1|1RB0LA|
|2|18371|4|6|1RB1LB_1LA1RC|
|3|14642600|6|14|1RB1RD_0RC1RB_1LC1LA|
|4|21216477565|13|107|1RB1LB_1LA0LC_1RE1LD_1RD0RA|
|5|51830926765032|4098|47176870|1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RF0LA|
|6|183593859414557127|?|? |1RB0LD_1RC0RF_1LC1LA_0LE1RG_1LF0RB_0RC0RE|

## Installation
### Dependencies
- `gmp`

### With Nix
```shell
nix build
```

### With Make
```shell
make
make install
```

## Usage
Getting the table:
```shell
States: 5
(0: Get Table 1: Get Number 2: Run)
Choice: 0
TM Number: 51830926765032
-----------------------------------
|   |  A  |  B  |  C  |  D  |  E  |
-----------------------------------
| 0 | 1RB | 1RC | 1RD | 1LA | 1RF |
| 1 | 1LC | 1RB | 0LE | 1LD | 0LA |
-----------------------------------
1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RF0LA

TM Number: 51830926765032
```
Getting the number:
```shell
States: 6
(0: Get Table 1: Get Number 2: Run)
Choice: 1
Std Format: 1RB0LD_1RC0RF_1LC1LA_0LE1RG_1LF0RB_0RC0RE
-----------------------------------------
|   |  A  |  B  |  C  |  D  |  E  |  F  |
-----------------------------------------
| 0 | 1RB | 1RC | 1LC | 0LE | 1LF | 0RC |
| 1 | 0LD | 0RF | 1LA | 1RG | 0RB | 0RE |
-----------------------------------------

TM Number: 183593859414557127
```
Running the machine:
```shell
States: 3
(0: Get Table 1: Get Number 2: Run)
Choice: 2
TM Number: 14642600
-----------------------
|   |  A  |  B  |  C  |
-----------------------
| 0 | 1RB | 0RC | 1LC |
| 1 | 1RD | 1RB | 1LA |
-----------------------
TM halted.
Ones (Σ): 6, Transitions (S): 14
```

## Contributing

Contributions are welcome!
Before submitting a pull request please:

- Format your code with `clang-format`
- Test your code with `valgrind`
