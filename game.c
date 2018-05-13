#define _CRT_SECURE_NO_WARNINGS

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include "c4.h"

enum { HUMAN = 0, COMPUTER = 1 };

static int get_num(char *prompt, int lower, int upper, int default_val);
static void print_board(int width, int height);
static void print_dot(void);
//static void apply_rule(int player, int *column, int *row);


static char piece[2] = { 'X', 'O' };

int
main()
{
	int player[2], level[2], turn = 0, num_of_players, move;
	int width, height, num_to_connect;
	int x1, y1, x2, y2;
	char buffer[80];

	printf("\n****  Welcome to the game of Connect!  ****\n\n");
	printf("By Whole Space\n");
	printf("May, 2018\n\n");

	width = 7;//get_num("Width of board", 1, 40, 7);
	height = 6;//get_num("Height of board", 1, 40, 6);
	num_to_connect = 4;//get_num("Number to connect", 1, 40, 4);

	player[0] = HUMAN;
	player[1] = COMPUTER;
	level[1] = 5; //get_num("Skill level of computer", 1, C4_MAX_LEVEL, 5);
	buffer[0] = '\0';
	num_of_players = 1;
	while (buffer[0] != 'y' && buffer[0] != 'n' && buffer[0] != '\n') {
		printf("Would you like to go first [y]? ");
		if (fgets(buffer, sizeof(buffer), stdin) == NULL) {
			printf("\nGoodbye!\n");
			exit(0);
		}
		buffer[0] = tolower(buffer[0]);
	}


	turn = (buffer[0] == 'n') ? 1 : 0;

	c4_new_game(width, height, num_to_connect);
	c4_poll(print_dot, CLOCKS_PER_SEC / 2);

	do {
		print_board(width, height);
		if (player[turn] == HUMAN) {
			do {
				sprintf(buffer, "Drop in which column");
				move = get_num(buffer, 1, width, -1) - 1;
			} while (!c4_make_move(turn, move, NULL));
		}
		else {
			sprintf(buffer, "Heuristic(1)? Or Rule(2)");
			int mode = 0;
			//scanf("%d", &mode);
			while (mode != 1 && mode != 2) {
				printf("select 1 or 2\n");
				mode = get_num(buffer, 1, 2, 0);
				//                scanf("%d", &mode);
			}
			if (mode == 1) {
				printf("\n**Heuristic**.\n\n");

				fflush(stdout);
				c4_auto_move(turn, level[turn], &move, NULL);

				printf("\nI dropped my piece into column %d.\n", move + 1);
				
			}
			else if (mode == 2) {
				printf("\n**Rule Based**\n\n");
				fflush(stdout);
				apply_rule(turn, &move, NULL);
				printf("\n\nI dropped my piece into column %d.\n", move + 1);

			}


		}
		/*
		else {
		if (num_of_players == 1)
		printf("Thinking.");
		else
		printf("Player %c is thinking.", piece[turn]);
		fflush(stdout);
		c4_auto_move(turn, level[turn], &move, NULL);
		if (num_of_players == 1)
		printf("\n\nI dropped my piece into column %d.\n", move+1);
		else
		printf("\n\nPlayer %c dropped its piece into column %d.\n",
		piece[turn], move+1);
		}*/

		turn = !turn;

	} while (!c4_is_winner(0) && !c4_is_winner(1) && !c4_is_tie());

	print_board(width, height);

	if (c4_is_winner(0)) {
		if (num_of_players == 1) {
			printf("You won!");
			
		}
	
		/*else
			printf("Player %c won!", piece[0]);*/
		c4_win_coords(&x1, &y1, &x2, &y2);
		printf("  (%d,%d) to (%d,%d)\n\n", y1 + 1, x1 + 1, y2 + 1, x2 + 1);
	}
	else if (c4_is_winner(1)) {
		if (num_of_players == 1) {
			printf("I won!");
			
			
		}
		
		c4_win_coords(&x1, &y1, &x2, &y2);
		printf("  (%d,%d) to (%d,%d)\n\n", y1 + 1, x1 + 1, y2 + 1, x2 + 1);
	}
	else {
		printf("There was a tie!\n\n");
		
	}

	c4_end_game();
	system("pause");  //강제종료가 되는 에러 수정 
	return 0;
	
}


/****************************************************************************/

static int
get_num(char *prompt, int lower, int upper, int default_value)
{
	int number = -1;
	int result;
	static char numbuf[40];

	do {

		printf("%s? ", prompt);

		if (fgets(numbuf, sizeof(numbuf), stdin) == NULL || numbuf[0] == 'q') {
			printf("\nGoodbye!\n");
			exit(0);
		}
		result = sscanf(numbuf, "%d", &number);
	} while (result == 0 || (result != EOF && (number<lower || number>upper)));

	return ((result == EOF) ? default_value : number);
}

/****************************************************************************/

static void
print_board(int width, int height)
{
	int x, y;
	char **board, spacing[2], dashing[2];

	board = c4_board();

	spacing[1] = dashing[1] = '\0';
	if (width > 19) {
		spacing[0] = '\0';
		dashing[0] = '\0';
	}
	else {
		spacing[0] = ' ';
		dashing[0] = '-';
	}

	printf("\n");
	for (y = height - 1; y >= 0; y--) {

		printf("|");
		for (x = 0; x<width; x++) {
			if (board[x][y] == C4_NONE)
				printf("%s %s|", spacing, spacing);
			else
				printf("%s%c%s|", spacing, piece[(int)board[x][y]], spacing);
		}
		printf("\n");

		printf("+");
		for (x = 0; x<width; x++)
			printf("%s-%s+", dashing, dashing);
		printf("\n");
	}

	printf(" ");
	for (x = 0; x<width; x++)
		printf("%s%d%s ", spacing, (x>8) ? (x + 1) / 10 : x + 1, spacing);
	if (width > 9) {
		printf("\n ");
		for (x = 0; x<width; x++)
			printf("%s%c%s ", spacing, (x>8) ? '0' + (x + 1) - ((x + 1) / 10) * 10 : ' ',
				spacing);
	}
	printf("\n\n");
}

/****************************************************************************/

static void
print_dot(void)
{
	printf(".");
	fflush(stdout);
}