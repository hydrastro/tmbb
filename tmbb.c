#include <stdio.h>
#include <stdlib.h>
#include <gmp.h>

typedef enum {
    ZERO,
    ONE
} tm_symbol_t;

typedef enum {
    LEFT,
    RIGHT
} tm_shift_t;

typedef struct tm_tape_cell {
    tm_symbol_t symbol;
    struct tm_tape_cell *left;
    struct tm_tape_cell *right;
} tm_tape_cell_t;

typedef struct tm_tape {
    tm_tape_cell_t *current_cell;
} tm_tape_t;

typedef int tm_state_t;

#define INVALID_STATE -1

typedef struct {
    tm_state_t next_state;
    tm_symbol_t write_symbol;
    tm_shift_t shift_direction;
} tm_transition_t;

typedef struct {
    tm_transition_t **table;
} tm_transition_table_t;

typedef struct tm_turing_machine {
    tm_tape_t *tape;
    tm_state_t current_state;
    tm_state_t final_state;
    tm_transition_table_t *transition_table;
    int ones_counter;
    int num_states;
    int num_transitions;
} tm_turing_machine_t;

tm_tape_cell_t* getRightCell(tm_tape_t *tape) {
    if (tape->current_cell->right == NULL) {
        tape->current_cell->right = (tm_tape_cell_t *)malloc(sizeof(tm_tape_cell_t));
        tape->current_cell->right->left = tape->current_cell;
        tape->current_cell->right->right = NULL;
        tape->current_cell->right->symbol = ZERO;
    }
    tape->current_cell = tape->current_cell->right;
    return tape->current_cell;
}

tm_tape_cell_t* getLeftCell(tm_tape_t *tape) {
    if (tape->current_cell->left == NULL) {
        tape->current_cell->left = (tm_tape_cell_t *)malloc(sizeof(tm_tape_cell_t));
        tape->current_cell->left->right = tape->current_cell;
        tape->current_cell->left->left = NULL;
        tape->current_cell->left->symbol = ZERO;
    }
    tape->current_cell = tape->current_cell->left;
    return tape->current_cell;
}

void writeOne(tm_tape_t *tape) {
    tape->current_cell->symbol = ONE;
}

void writeZero(tm_tape_t *tape) {
    tape->current_cell->symbol = ZERO;
}

void halt() {
    exit(0);
}

tm_transition_table_t* initialize_transition_table(int num_states) {
    tm_transition_table_t *table = (tm_transition_table_t *)malloc(sizeof(tm_transition_table_t));
    table->table = (tm_transition_t **)malloc(num_states * sizeof(tm_transition_t *));

    for (int i = 0; i < num_states; ++i) {
        table->table[i] = (tm_transition_t *)malloc(2 * sizeof(tm_transition_t)); 
        for (int j = 0; j < 2; ++j) {
            table->table[i][j].next_state = INVALID_STATE;
        }
    }

    return table;
}

void set_transition(tm_transition_table_t *table, tm_state_t current_state, tm_symbol_t read_symbol,
                    tm_state_t next_state, tm_symbol_t write_symbol, tm_shift_t shift_direction) {
    table->table[current_state][read_symbol].next_state = next_state;
    table->table[current_state][read_symbol].write_symbol = write_symbol;
    table->table[current_state][read_symbol].shift_direction = shift_direction;
}

void generate_transition_table(tm_turing_machine_t *tm, mpz_t number) {
    int states = tm->num_states;
    int bases[states * 6];
    int output[states * 6];

    // machines ordering: next_state->shift_direction->write_char
    // starting from the last state, from read character 1
    // 0LA -> 0LB -> 0RA -> 0RB -> 1LA -> 1LB -> 1RA -> 1RB -> next state
    // reverse order of cardinalities: write (2), shift (2), next (n+1)
    for (int i = 0; i < states * 2; i++) {
        bases[i * 3] = states + 1;
        bases[i * 3 + 1] = 2;
        bases[i * 3 + 2] = 2;
    }

    mpz_t temp_number, temp_base, temp_output;
    mpz_inits(temp_number, temp_base, temp_output, NULL);
    mpz_set(temp_number, number);
    for (int j = 0; j < states * 6; j++) {
        mpz_set_ui(temp_base, bases[j]);
        mpz_mod(temp_output, temp_number, temp_base);
        output[states * 6 - j - 1] = mpz_get_ui(temp_output);
        mpz_fdiv_q(temp_number, temp_number, temp_base);
    }

    mpz_clears(temp_number, temp_base, temp_output, NULL);

    for(int i = 0; i < states; i++) {
        for(int j = 0; j < 2; j++) {
            int idx = (i * 6) + (j * 3);
            set_transition(tm->transition_table, i, j,
                output[idx + 2],
                output[idx],
                output[idx + 1] ? RIGHT : LEFT);
        }
    }
}

void get_turing_machine_number(mpz_t result, tm_turing_machine_t *tm) {
    int states = tm->num_states;
    int bases[states * 6];

    mpz_t weight, temp;
    mpz_inits(weight, temp, NULL);
    mpz_set_ui(result, 0);
    mpz_set_ui(weight, 1);
    for (int i = 0; i < states * 2; i++) {
        bases[i * 3] = 2;
        bases[i * 3 + 1] = 2;
        bases[i * 3 + 2] = states + 1;
    }

    for (int i = states - 1; i >= 0; i--) {
        for (int j = 1; j >= 0; j--) {
            // here order matters
            tm_transition_t transition = tm->transition_table->table[i][j];

            mpz_set_ui(temp, transition.next_state);
            mpz_mul(temp, temp, weight);
            mpz_add(result, result, temp);
            mpz_mul_ui(weight, weight, bases[i * 6 + j * 3 + 2]);

            if (transition.shift_direction == RIGHT) {
                mpz_add(result, result, weight);
            }
            mpz_mul_ui(weight, weight, bases[i * 6 + j * 3 + 1]);

            if (transition.write_symbol == ONE) {
                mpz_add(result, result, weight);
            }
            mpz_mul_ui(weight, weight, bases[i * 6 + j * 3]);
        }
    }

    mpz_clears(weight, temp, NULL);
}

void process_transition(tm_turing_machine_t *tm) {
    tm_transition_t *t = &tm->transition_table->table[tm->current_state][tm->tape->current_cell->symbol];

    if (tm->tape->current_cell->symbol == ZERO && t->write_symbol == ONE) {
        tm->ones_counter++;
    }
    if (tm->tape->current_cell->symbol == ONE && t->write_symbol == ZERO) {
        tm->ones_counter--;
    }
    tm->num_transitions++;

    if (t->next_state == INVALID_STATE) {
        printf("Invalid state, halting execution.");
        halt();
    }

    tm->tape->current_cell->symbol = t->write_symbol;
    tm->current_state = t->next_state;

    if (t->shift_direction == LEFT) {
        getLeftCell(tm->tape);
    } else {
        getRightCell(tm->tape);
    }
}

void run_turing_machine(tm_turing_machine_t *tm) {
    while (tm->current_state != tm->final_state) {
        // TODO: bottom limit
        process_transition(tm);
    }
    printf("TM halted.\n");
    printf("Ones (Σ): %d, Transitions (S): %d\n", tm->ones_counter, tm->num_transitions);
    halt();
}

tm_turing_machine_t* initialize_tm(int num_states, tm_state_t initial_state, tm_state_t final_state) {
    tm_turing_machine_t *tm = (tm_turing_machine_t *)malloc(sizeof(tm_turing_machine_t));
    tm->tape = (tm_tape_t *)malloc(sizeof(tm_tape_t));

    tm->tape->current_cell = (tm_tape_cell_t *)malloc(sizeof(tm_tape_cell_t));
    tm->tape->current_cell->left = NULL;
    tm->tape->current_cell->right = NULL;
    tm->tape->current_cell->symbol = ZERO;

    tm->current_state = initial_state;
    tm->final_state = final_state;
    tm->num_states = num_states;
    tm->num_transitions = 0;
    tm->transition_table = initialize_transition_table(num_states);
    tm->ones_counter = 0;

    return tm;
}
void print_transition_table(tm_turing_machine_t *tm) {
    tm_transition_table_t *table = tm->transition_table;

    printf("-----");
    for (int state = 0; state < tm->num_states; ++state) {
        printf("------");
    }
    printf("\n");
    printf("|   |");

    for (int state = 0; state < tm->num_states; ++state) {
        printf("  %c  |", 'A' + state);
    }
    printf("\n");
    printf("-----");
    for (int state = 0; state < tm->num_states; ++state) {
        printf("------");
    }
    printf("\n");

    printf("| 0 |");
    for (int state = 0; state < tm->num_states; ++state) {
        tm_transition_t *transition = &table->table[state][0];
        printf(" %d%c%c |", transition->write_symbol, transition->shift_direction == LEFT ? 'L' : 'R', 'A' + transition->next_state);
    }
    printf("\n");

    printf("| 1 |");
    for (int state = 0; state < tm->num_states; ++state) {
        tm_transition_t *transition = &table->table[state][1];
        printf(" %d%c%c |", transition->write_symbol, transition->shift_direction == LEFT ? 'L' : 'R', 'A' + transition->next_state);
    }
    printf("\n");
    printf("-----");
    for (int state = 0; state < tm->num_states; ++state) {
        printf("------");
    }
    printf("\n");
}

void print_transition_table2(tm_turing_machine_t *tm) {
    tm_transition_table_t *table = tm->transition_table;
    for ( int state = 0; state < tm->num_states; ++state) {
        for (int symbol = 0; symbol <= 1; ++symbol) {
            tm_transition_t *transition = &table->table[state][symbol];
            if (transition->next_state == INVALID_STATE) {
                continue;
            }
            printf("%d%d%d",transition->next_state, transition->write_symbol,transition->shift_direction);
        }
    }
    printf("\n");
}

void parse_transition_table(tm_turing_machine_t *tm, const char *input) {
    int num_states = tm->num_states;
    int idx = 0;

    for (int i = 0; i < num_states; i++) {
        for (int j = 0; j < 2; j++) {
            char next_state_char = input[idx + 2];
            int next_state = next_state_char - 'A';

            tm_symbol_t write_symbol = (input[idx] == '1') ? ONE : ZERO;

            tm_shift_t shift_direction = (input[idx + 1] == 'R') ? RIGHT : LEFT;

            set_transition(tm->transition_table, i, j, next_state, write_symbol, shift_direction);
            idx += 3;
        }
        idx++;
    }
}
/*
state space: |states|, |tms| ( =(4(n+1))^(2n) )
1, 1
2, 64
3, 20736
4, 16777216
5, 25600000000
6, 63403380965376
7, 232218265089212416
8, 1180591620717411303424
9, 7958661109946400884391936
10, 68719476736000000000000000000
11, 739696442014594807059393047166976
12, 9711967541295580042210555933809967104
13, 152784834199652075368661148843397208866816

busy beavers: |states|, tm number, |ones|, |transitions| (std format)
1, 56, 1, 1
2, 18371, 4, 6 (1RB1LB_1LA1RC)
3, 14642600, 6, 14 (1RB1RD_0RC1RB_1LC1LA)
4, 21216477565, 13, 107 (1RB1LB_1LA0LC_1RE1LD_1RD0RA)
5, 51830926765032, 4098, 47176870 (1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RF0LA)
6, 183593859414557127, ?, ?  (1RB0LD_1RC0RF_1LC1LA_0LE1RG_1LF0RB_0RC0RE)
*/

int main() {
    int num_states, choice;
    char input[1024];
    mpz_t tm_no;
    mpz_init(tm_no);

    printf("States: ");
    if(scanf("%d", &num_states) != 1) {
        return -1;
    }

    printf("(0: Get Table 1: Get Number 2: Run)\nChoice: ");
    if(scanf("%d", &choice) != 1) {
        return -1;
    }

    tm_turing_machine_t *tm = initialize_tm(num_states, 0, num_states);

    if (choice == 0) {
        printf("TM Number: ");
        gmp_scanf("%Zd", tm_no);

        generate_transition_table(tm, tm_no);
        print_transition_table(tm);
        mpz_t tm_number;
        mpz_init(tm_number);


        get_turing_machine_number(tm_number, tm);
        gmp_printf("\nTM Number: %Zd\n", tm_number);

    } else if (choice == 1) {
        int j, k, l;

        printf("Std Format: ");
        if(scanf("%s", input) != 1) {
            return -1;
        }
        parse_transition_table(tm, input);

        mpz_t tm_number;
        mpz_init(tm_number);

        print_transition_table(tm);

        get_turing_machine_number(tm_number, tm);
        gmp_printf("\nTM Number: %Zd\n", tm_number);

        mpz_clear(tm_number);

    } else if (choice == 2) {
        printf("TM Number: ");
        gmp_scanf("%Zd", tm_no);

        generate_transition_table(tm, tm_no);
        print_transition_table(tm);

        run_turing_machine(tm);
    } else {
        printf("No.\n");
    }

    mpz_clear(tm_no);

    return 0;
}
