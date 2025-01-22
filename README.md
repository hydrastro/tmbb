# Turing Machines & Busy Beavers

A little program for playing around with Turing Machines.

## Features
- Calculation of the Turing Machine's number, given its transition table
- Calculation of the Turing Machine's transition table, given its number
- Simulation of Turing Machines (and Busy Beavers number calculation)


### Turing Machines
State space size:  `( =(4(n+1))^(2n) )`

|states|tms|
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
|states|tm number|ones|transitions|std format|
|------|---------|----|-----------|----------|
|1|56|1|1|1RB0LA|
|2|18371|4|6|1RB1LB_1LA1RC|
|3|14642600|6|14|1RB1RD_0RC1RB_1LC1LA|
|4|21216477565|13|107|1RB1LB_1LA0LC_1RE1LD_1RD0RA|
|5|51830926765032|4098|47176870|1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RF0LA|
|6|183593859414557127|?|? |1RB0LD_1RC0RF_1LC1LA_0LE1RG_1LF0RB_0RC0RE|

## Installation
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


## Contributing

Contributions are welcome!
Before submitting a pull request please:

- format your code with `clang-format`
- test your code with `valgrind`
