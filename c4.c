#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <assert.h>
#include "c4.h"

/* Some macros for convenience. */

#define other(x)        ((x) ^ 1)
#define real_player(x)  ((x) & 1)

#define pop_state() \
(current_state = &state_stack[--depth])

/* The "goodness" of the current state with respect to a player is the */
/* score of that player minus the score of the player's opponent.  A   */
/* positive value will result if the specified player is in a better   */
/* situation than his/her opponent.                                    */

#define goodness_of(player) \
(current_state->score[player] - current_state->score[other(player)])

/* A local struct which defines the state of a game. */

typedef struct {

	char **board;           /* The board configuration of the game state.  */
							/* board[x][y] specifies the position of the   */
							/* xth column and the yth row of the board,    */
							/* where column and row numbering starts at 0. */
							/* (The 0th row is the bottom row.)            */
							/* A value of 0 specifies that the position is */
							/* occupied by a piece owned by player 0, a    */
							/* value of 1 specifies that the position is   */
							/* occupied by a piece owned by player 1, and  */
							/* a value of C4_NONE specifies that the       */
							/* position is unoccupied.                     */

	int *(score_array[2]);  /* An array specifying statistics on both      */
							/* players.  score_array[0] specifies the      */
							/* statistics for player 0, while              */
							/* score_array[1] specifies the statistics for */
							/* player 1.                                   */

	int score[2];           /* The actual scores of each player, deducible */
							/* from score_array, but kept separately for   */
							/* efficiency.  The score of player x is the   */
							/* sum of score_array[x].  A score is          */
							/* basically a function of how many winning    */
							/* positions are still available to the        */
							/* and how close he/she is to achieving each   */
							/* of these positions.                         */

	short int winner;       /* The winner of the game - either 0, 1 or     */
							/* C4_NONE.  Deducible from score_array, but   */
							/* kept separately for efficiency.             */

	int num_of_pieces;      /* The number of pieces currently occupying    */
							/* board spaces.  Deducible from board, but    */
							/* kept separately for efficiency.             */

} Game_state;

/* Static global variables. */

static int size_x, size_y, total_size;
static int num_to_connect;
static int win_places;

static int ***map;  /* map[x][y] is an array of win place indices, */
					/* terminated by a -1.                         */

static int magic_win_number;
static bool game_in_progress = false, move_in_progress = false;
static bool seed_chosen = false;
static void(*poll_function)(void) = NULL;
static clock_t poll_interval, next_poll;
static Game_state state_stack[C4_MAX_LEVEL + 1];
static Game_state *current_state;
static int depth;
static int states_allocated = 0;
static int *drop_order;

/* A declaration of the local functions. */

static int num_of_win_places(int x, int y, int n);
static void update_score(int player, int x, int y);
static int drop_piece(int player, int column);
static void push_state(void);
static int evaluate(int player, int level, int alpha, int beta);
static void *emalloc(size_t size);

static int eval_rule(int ruleOfCol[]);


/****************************************************************************/
/**                                                                        **/
/**  This function is used to specify a poll function and the interval at  **/
/**  which it should be called.  A poll function can be used, for example, **/
/**  to tend to any front-end interface tasks, such as updating graphics,  **/
/**  etc.  The specified poll function should accept void and return void. **/
/**  The interval unit is 1/CLOCKS_PER_SEC seconds of processor time.      **/
/**  Therefore, specifying CLOCKS_PER_SEC as the interval will cause the   **/
/**  poll function to be called once every second of processor time, while **/
/**  specifying CLOCKS_PER_SEC/4 will cause it to be called once every     **/
/**  1/4 second of processor time.                                         **/
/**                                                                        **/
/**  If no polling is required, the poll function can be specified as      **/
/**  NULL.  This is the default.                                           **/
/**                                                                        **/
/**  This function can be called an arbitrary number of times throughout   **/
/**  any game.                                                             **/
/**                                                                        **/
/**  It is illegal for the specified poll function to call the functions   **/
/**  c4_make_move(), c4_auto_move(), c4_end_game() or c4_reset().          **/
/**                                                                        **/
/****************************************************************************/

void
c4_poll(void(*poll_func)(void), clock_t interval)
{
	poll_function = poll_func;
	poll_interval = interval;
}


/****************************************************************************/
/**                                                                        **/
/**  This function sets up a new game.  This must be called exactly once   **/
/**  before each game is started.  Before it can be called a second time,  **/
/**  end_game() must be called to destroy the previous game.               **/
/**                                                                        **/
/**  width and height are the desired dimensions of the game board, while  **/
/**  num is the number of pieces required to connect in a row in order to  **/
/**  win the game.                                                         **/
/**                                                                        **/
/****************************************************************************/

void
c4_new_game(int width, int height, int num)
{
	register int i, j, k, x;
	int win_index, column;
	int *win_indices;

	assert(!game_in_progress);
	assert(width >= 1 && height >= 1 && num >= 1);

	size_x = width;
	size_y = height;
	total_size = width * height;
	num_to_connect = num;
	magic_win_number = 1 << num_to_connect;
	win_places = num_of_win_places(size_x, size_y, num_to_connect);

	/* Set up a random seed for making random decisions when there is */
	/* equal goodness between two moves.                              */

	if (!seed_chosen) {
		srand((unsigned int)time((time_t *)0));
		seed_chosen = true;
	}

	/* Set up the board */

	depth = 0;
	current_state = &state_stack[0];

	current_state->board = (char **)emalloc(size_x * sizeof(char *));
	for (i = 0; i<size_x; i++) {
		current_state->board[i] = (char *)emalloc(size_y);
		for (j = 0; j<size_y; j++)
			current_state->board[i][j] = C4_NONE;
	}

	/* Set up the score array */

	current_state->score_array[0] = (int *)emalloc(win_places * sizeof(int));
	current_state->score_array[1] = (int *)emalloc(win_places * sizeof(int));
	for (i = 0; i<win_places; i++) {
		current_state->score_array[0][i] = 1;
		current_state->score_array[1][i] = 1;
	}

	current_state->score[0] = current_state->score[1] = win_places;
	current_state->winner = C4_NONE;
	current_state->num_of_pieces = 0;

	states_allocated = 1;

	/* Set up the map */

	map = (int ***)emalloc(size_x * sizeof(int **));
	for (i = 0; i<size_x; i++) {
		map[i] = (int **)emalloc(size_y * sizeof(int *));
		for (j = 0; j<size_y; j++) {
			map[i][j] = (int *)emalloc((num_to_connect * 4 + 1) * sizeof(int));
			map[i][j][0] = -1;
		}
	}

	win_index = 0;

	/* Fill in the horizontal win positions */
	for (i = 0; i<size_y; i++)
		for (j = 0; j<size_x - num_to_connect + 1; j++) {
			for (k = 0; k<num_to_connect; k++) {
				win_indices = map[j + k][i];
				for (x = 0; win_indices[x] != -1; x++)
					;
				win_indices[x++] = win_index;
				win_indices[x] = -1;
			}
			win_index++;
		}

	/* Fill in the vertical win positions */
	for (i = 0; i<size_x; i++)
		for (j = 0; j<size_y - num_to_connect + 1; j++) {
			for (k = 0; k<num_to_connect; k++) {
				win_indices = map[i][j + k];
				for (x = 0; win_indices[x] != -1; x++)
					;
				win_indices[x++] = win_index;
				win_indices[x] = -1;
			}
			win_index++;
		}

	/* Fill in the forward diagonal win positions */
	for (i = 0; i<size_y - num_to_connect + 1; i++)
		for (j = 0; j<size_x - num_to_connect + 1; j++) {
			for (k = 0; k<num_to_connect; k++) {
				win_indices = map[j + k][i + k];
				for (x = 0; win_indices[x] != -1; x++)
					;
				win_indices[x++] = win_index;
				win_indices[x] = -1;
			}
			win_index++;
		}

	/* Fill in the backward diagonal win positions */
	for (i = 0; i<size_y - num_to_connect + 1; i++)
		for (j = size_x - 1; j >= num_to_connect - 1; j--) {
			for (k = 0; k<num_to_connect; k++) {
				win_indices = map[j - k][i + k];
				for (x = 0; win_indices[x] != -1; x++)
					;
				win_indices[x++] = win_index;
				win_indices[x] = -1;
			}
			win_index++;
		}

	/* Set up the order in which automatic moves should be tried. */
	/* The columns nearer to the center of the board are usually  */
	/* better tactically and are more likely to lead to a win.    */
	/* By ordering the search such that the central columns are   */
	/* tried first, alpha-beta cutoff is much more effective.     */

	drop_order = (int *)emalloc(size_x * sizeof(int));
	column = (size_x - 1) / 2;
	for (i = 1; i <= size_x; i++) {
		drop_order[i - 1] = column;
		column += ((i % 2) ? i : -i);
	}

	game_in_progress = true;
}


/****************************************************************************/
/**                                                                        **/
/**  This function drops a piece of the specified player into the          **/
/**  specified column.  A value of true is returned if the drop is         **/
/**  successful, or false otherwise.  A drop is unsuccessful if the        **/
/**  specified column number is invalid or full.  If the drop is           **/
/**  successful and row is a non-NULL pointer, the row where the piece     **/
/**  ended up is returned through the row pointer.  Note that column and   **/
/**  row numbering start at 0.                                             **/
/**                                                                        **/
/****************************************************************************/

bool
c4_make_move(int player, int column, int *row)
{
	assert(game_in_progress);
	assert(!move_in_progress);

	if (column >= size_x || column < 0)
		return false;

	int result = drop_piece(real_player(player), column);
	if (row != NULL && result >= 0)
		*row = result;
	return (result >= 0);
}


/****************************************************************************/
/**                                                                        **/
/**  This function instructs the computer to make a move for the specified **/
/**  player.  level specifies the number of levels deep the computer       **/
/**  should search the game tree in order to make its decision.  This      **/
/**  corresponds to the number of "moves" in the game, where each player's **/
/**  turn is considered a move.  A value of true is returned if a move was **/
/**  made, or false otherwise (i.e. if the board is full).  If a move was  **/
/**  made, the column and row where the piece ended up is returned through **/
/**  the column and row pointers (unless a pointer is NULL, in which case  **/
/**  it won't be used to return any information).  Note that column and    **/
/**  row numbering start at 0.  Also note that for a standard 7x6 game of  **/
/**  Connect-4, the computer is brain-dead at levels of three or less,     **/
/**  while at levels of four or more the computer provides a challenge.    **/
/**                                                                        **/
/****************************************************************************/

bool
c4_auto_move(int player, int level, int *column, int *row)
{
	int best_column = -1, goodness = 0, best_worst = -(INT_MAX);
	int num_of_equal = 0, real_player, current_column, result;

	assert(game_in_progress);
	assert(!move_in_progress);
	assert(level >= 1 && level <= C4_MAX_LEVEL);

	real_player = real_player(player);

	/* It has been proven that the best first move for a standard 7x6 game  */
	/* of connect-4 is the center column.  See Victor Allis' masters thesis */
	/* ("ftp://ftp.cs.vu.nl/pub/victor/connect4.ps") for this proof.        */

	if (current_state->num_of_pieces < 1 &&
		size_x == 7 && size_y == 6 && num_to_connect == 4 &&
		(current_state->num_of_pieces == 0 ||
			current_state->board[3][0] != C4_NONE)) {
		if (column != NULL)
			*column = 2;
		if (row != NULL)
			*row = current_state->num_of_pieces;
		drop_piece(real_player, 2);
		printf("coordinate : (1, %d)\n", *column+1);
		return true;
	}

	if (current_state->num_of_pieces == 1) {
		if (column != NULL)
			*column = 3;
		if (row != NULL)
			*row = current_state->num_of_pieces;
		drop_piece(real_player, 3);
		printf("coordinate : (1, %d)\n", *column+1);
		return true;
	}


	move_in_progress = true;

	/* Simulate a drop in each of the columns and see what the results are. */

	for (int i = 0; i<size_x; i++) {
		push_state();
		current_column = drop_order[i];

		result = drop_piece(real_player, current_column);

		/* If this column is full, ignore it as a possibility. */
		if (result < 0) {
			pop_state();
			continue;
		}

		/* If this drop wins the game, take it! */
		else if (current_state->winner == real_player) {
			best_column = current_column;
			pop_state();
			break;
		}

		/* Otherwise, look ahead to see how good this move may turn out */
		/* to be (assuming the opponent makes the best moves possible). */
		else {
			next_poll = clock() + poll_interval;
			goodness = evaluate(real_player, level, -(INT_MAX), -best_worst);
		}

		/* If this move looks better than the ones previously considered, */
		/* remember it.                                                   */
		if (goodness > best_worst) {
			best_worst = goodness;
			best_column = current_column;
			num_of_equal = 1;
		}

		/* If two moves are equally as good, make a random decision. */
		else if (goodness == best_worst) {
			num_of_equal++;
			if ((rand() >> 4) % num_of_equal == 0)
				best_column = current_column;
		}

		pop_state();
	}

	move_in_progress = false;

	/* Drop the piece in the column decided upon. */

	if (best_column >= 0) {
		result = drop_piece(real_player, best_column);
		if (column != NULL)
			*column = best_column;
		if (row != NULL)
			*row = result;
		printf("coordinate : (%d, %d)\n",result+1 , *column + 1);
		return true;
	}
	else
		return false;
}

/////////////****************rule function*********************///////////////
int ruleflag[7];
//int rule_index;
int ruleOfCol[7][8] = { 0 };

void apply_rule(int player, int *column, int *row) {
	int max = -300001;
	int max_col = -100000;


	int real_player, result;

	assert(game_in_progress);
	assert(!move_in_progress);


	real_player = real_player(player);

	//중간칼럼 더 점수 높게
	for (int i = 0; i<4; i++) {
		ruleflag[i] = i + 5;
	}
	for (int i = 4; i<7; i++) {
		ruleflag[i] = ruleflag[6 - i];
	}

	if (current_state->num_of_pieces < 1) {
		if (column != NULL)
			*column = 2;  
		if (row != NULL)
			*row = current_state->num_of_pieces;
		int r=drop_piece(real_player, 2);
		printf("I chosed the rule 0\n");
		printf("coordinate : (%d, %d)\n", r+1, *column + 1);
		return;
	}

	else if (current_state->num_of_pieces < 4) {
		if (column != NULL)
			*column = 3;  
		if (row != NULL)
			*row = current_state->num_of_pieces;
		int r=drop_piece(real_player, 3);
		printf("I chosed the rule 0\n");
		printf("coordinate : (%d, %d)\n", r + 1, *column + 1);
		return;
	}



	for (int i = 0; i<7; i++) {
		push_state();
		int numrow = drop_piece(real_player, i);
		if (numrow == -1) {
			ruleflag[i] = -300000;
			//      printf("ruleflag%d= %d\n", i + 1, ruleflag[i]);
			pop_state();
			continue;
		}

		else {
			ruleflag[i] += eval_rule(ruleOfCol[i]);
			//       printf("ruleflag%d= %d\n", i + 1, ruleflag[i]);
			pop_state();

		}
	}

	for (int i = 0; i<7; i++) {
		if (max<ruleflag[i]) {
			max = ruleflag[i];
			max_col = i;
		}
	}

	result = drop_piece(real_player, max_col);
	//    printf("I chosed the rule %d\n", rule_index+1);

	

	for (int i = 0; i < 8; i++) {
		if (ruleOfCol[max_col][i] > 0)
			printf("I chosed the rule %d\n", ruleOfCol[max_col][i]);
	}
	

	if (column != NULL)
		*column = max_col;
	if (row != NULL) 
		*row = result;
	printf("coordinate : (%d, %d)\n", result + 1, *column + 1);
	return;

}

int eval_rule(int nthCol[]) {
	int score = 0;
	int total = 0;
	int rule[8];
	for (int k = 0; k < 8; k++) {
		rule[k] = 0;
	}
	for (int i = 0; i <= 6; i++) {//행
		for (int j = 0; j <= 5; j++) {//렬
									  /*rule 1*/  //AI 가 4줄이 되면 바로 놓는다.
			if (i < 4 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 1 && current_state->board[i + 2][j] == 1 && current_state->board[i + 3][j] == 1) {
				/*   if (i > 0 && current_state->board[i][j-1] != C4_NONE && current_state->board[i + 1][j - 1] != C4_NONE && current_state->board[i + 2][j - 1] != C4_NONE && current_state->board[i + 3][j - 1] != C4_NONE) {
				//가로*/
				score = 5000000;
				rule[0] += score;
				//   printf("1-1\n");
				//}
			}
			/* 시행착오
			//first line
			else if (j == 0 && i < 4 && current_state->board[i][j] == 1 && current_state->board[i+1][j] == 1 && current_state->board[i+2][j] == 1 && current_state->board[i+3][j] == 1) {
			score = 500000;
			rule[0] += score;
			}*/

			else if (j<3 && current_state->board[i][j] == 1 && current_state->board[i][j + 1] == 1 && current_state->board[i][j + 2] == 1 && current_state->board[i][j + 3] == 1) {
				score = 5000000;
				rule[0] += score;
				//세로
			}
			else if (i < 4 && j < 3 && current_state->board[i][j] == 1 && current_state->board[i + 1][j + 1] == 1 && current_state->board[i + 2][j + 2] == 1 && current_state->board[i + 3][j + 3] == 1) {
				/*   if (current_state->board[i][j-1] != C4_NONE && current_state->board[i+1][j - 1] != C4_NONE && current_state->board[i + 2][j + 1] != C4_NONE && current_state->board[i + 3][j + 2] != C4_NONE) {*/
				score = 5000000;
				rule[0] += score;
				//대각선 오름차순
				//    }
			}
			//first line
			/*   else if (i < 4 && j == 0 && current_state->board[i][j] == 1 && current_state->board[i + 1][j + 1] == 1 && current_state->board[i + 2][j + 2] == 1 && current_state->board[i + 3][j + 3] == 1) {
			score = 5000000;
			rule[0] += score;
			//대각선 오름차순
			}*/


			else if (j > 2 && i<4 && current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == 1 && current_state->board[i + 3][j - 3] == 1) {
				/*     if (i > 3 && current_state->board[i][j-1] != C4_NONE && current_state->board[i +1][j - 2] != C4_NONE && current_state->board[i + 2][j - 3] != C4_NONE && current_state->board[i + 3][j - 4] != C4_NONE) {*/
				score = 5000000;
				rule[0] += score;
				//      }
				//대각선 내림차순
			}
			//first line
			/*     else if (j == 3 && i<4 && current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == 1 && current_state->board[i + 3][j - 3] == 1) {
			score = 5000000;
			rule[0] += score;
			//대각선 내림차순
			}*/


			/*rule 2*/  //인간 돌이 4줄이 되면 막는다.
			if (i < 4 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 0 && current_state->board[i + 2][j] == 0 && current_state->board[i + 3][j] == 0) {
				if (i < 3 && current_state->board[i + 4][j] == 1) {
					score = 300000;
					rule[1] += score;
				}
				score = 250000;
				rule[1] += score;
				//horizontal OXXX_(_!=X)
			}
			/*
			//first line
			if (j == 0 && i < 4 && current_state->board[i][j] == 1 && current_state->board[i+1][j] == 0 && current_state->board[i+2][j] == 0 && current_state->board[i+3][j] == 0) {
			if (i < 3 && current_state->board[i+4][j] == 1) {
			score = 300000;
			rule[1] += score;
			}
			score = 250000;
			rule[1] += score;
			//horizontal OXXX_(_!=X)
			}*/

			if (i < 3 && current_state->board[i][j] == 0 && current_state->board[i + 1][j] == 0 && current_state->board[i + 2][j] == 0 && current_state->board[i + 3][j] == 1) {
				if (i > 0 && current_state->board[i - 1][j] == 1) {
					score = 300000;
					rule[1] += score;
				}
				score = 250000;
				rule[1] += score;
				//horizontal _XXXO(_!=X)
			}
			/*
			//first line
			if (j == 0 && i < 4 && current_state->board[i][j] == 0 && current_state->board[i+1][j] == 0 && current_state->board[i+2][j] == 0 && current_state->board[i+3][j] == 1) {
			score = 250000;
			rule[1] += score;
			//horizontal _XXXO(_!=X)
			}
			*/

			if (i < 4 && current_state->board[i][j] == 0 && current_state->board[i + 1][j] == 0 && current_state->board[i + 2][j] == 1 && current_state->board[i + 3][j] == 0) {
				//  if (current_state->board[i +2][j-1] != C4_NONE) {
				score = 250000;
				rule[1] += score;
				//  printf("2-5\n");
				//   }
				//horizontal XXOX
			}
			/*
			//first line
			if (j == 0 && i < 4 && current_state->board[i][j] == 0 && current_state->board[i+1][j] == 0 && current_state->board[i+2][j] == 1 && current_state->board[i+3][j] == 0) {
			score = 250000;
			rule[1] += score;
			//horizontal XXOX
			//    printf("2-6\n");
			}*/

			if (i < 4 && current_state->board[i][j] == 0 && current_state->board[i + 1][j] == 1 && current_state->board[i + 2][j] == 0 && current_state->board[i + 3][j] == 0) {
				// if (current_state->board[i + 1][j - 1] != C4_NONE) {
				score = 250000;
				rule[1] += score;
				//     printf("2-7\n");
				// }   //horizontal XOXX
			}
			/*
			//first line
			if (j == 0 && i < 4 && current_state->board[i][j] == 0 && current_state->board[i+1][j] == 1 && current_state->board[i+2][j] == 0 && current_state->board[i+3][j] == 0) {
			score = 250000;
			rule[1] += score;
			//horizontal XOXX
			//  printf("2-8\n");
			}*/

			if (j<3 && current_state->board[i][j] == 0 && current_state->board[i][j + 1] == 0 && current_state->board[i][j + 2] == 0 && current_state->board[i][j + 3] == 1) {
				if (j > 0 && current_state->board[i][j - 1] == 1) {//
					score = 300000;
					rule[1] += score;
				}
				//return 250; 시행착오
				score = 250000;
				rule[1] += score;
				//  printf("2-9\n");
			} //vertical

			if (j < 3 && i < 4 && current_state->board[i][j] == 1 && current_state->board[i + 1][j + 1] == 0 && current_state->board[i + 2][j + 2] == 0 && current_state->board[i + 3][j + 3] == 0) {
				if (i < 3 && j < 2 && current_state->board[i + 4][j + 4] == 1) {//
					score = 300000;
					rule[1] += score;
				}
				//    if (current_state->board[i + 4][j + 3] != C4_NONE) {
				score = 250000;
				rule[1] += score;
				//      printf("2-10\n");
				//  }
				//diagonal OXXX_(_!=X) ascending
			}
			/*
			//first line
			if (j == 0 && i < 4 && current_state->board[i][j] == 1 && current_state->board[i + 1][j + 1] == 0 && current_state->board[i + 2][j + 2] == 0 && current_state->board[i + 3][j + 3] == 0) {
			score = 250000;
			rule[1] += score;
			//      printf("2-10\n");
			//diagonal OXXX_(_!=X) ascending
			}*/


			if (j < 3 && i < 4 && current_state->board[i][j] == 0 && current_state->board[i + 1][j + 1] == 0 && current_state->board[i + 2][j + 2] == 0 && current_state->board[i + 3][j + 3] == 1) {
				if (i > 0 && j > 0 && current_state->board[i - 1][j - 1] == 1) {
					score = 300000;
					rule[1] += score;
				} 
				  //      if (current_state->board[i][j-1] != C4_NONE && current_state->board[i + 4][j + 3] != C4_NONE) {
				score = 250000;
				rule[1] += score;
				//       printf("2-11\n");
				//        }

				//diagonal _XXXO(_!=X) ascending
			}
			/*
			//first line
			if (j == 0 && j < 3 && i < 4 && current_state->board[i][j] == 0 && current_state->board[i + 1][j + 1] == 0 && current_state->board[i + 2][j + 2] == 0 && current_state->board[i + 3][j + 3] == 1) {
			score = 250000;
			rule[1] += score;
			//   printf("2-12\n");
			//diagonal _XXXO(_!=X) ascending
			}

			*/
			if (j < 3 && i < 4 && current_state->board[i][j] == 0 && current_state->board[i + 1][j + 1] == 0 && current_state->board[i + 2][j + 2] == 1 && current_state->board[i + 3][j + 3] == 0) {
				//      if (current_state->board[i + 2][j + 1] != C4_NONE) {
				score = 250000;
				rule[1] += score;
				//   printf("2-13\n");
				//    }

				//diagonal XXOX ascending
			}

			if (j < 3 && i < 4 && current_state->board[i][j] == 0 && current_state->board[i + 1][j + 1] == 1 && current_state->board[i + 2][j + 2] == 0 && current_state->board[i + 3][j + 3] == 0) {
				//       if (current_state->board[i+1][j] != C4_NONE) {
				score = 250000;
				rule[1] += score;
				//     printf("2-14\n");
				//     }

				//diagonal XOXX ascending
			}

			if (j > 2 && i < 4 && current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == 0 && current_state->board[i + 2][j - 2] == 0 && current_state->board[i + 3][j - 3] == 0) {
				if (i < 3 && j > 3 && current_state->board[i + 4][j - 4] == 1) { //
					score = 300000;
				}
				//    if (j > 4 && i>3 && current_state->board[i][j-1] != C4_NONE && current_state->board[i + 4][j - 5] != C4_NONE) {
				score = 250000;
				rule[1] += score;
				//   printf("2-15\n");

				//  }
				//diagonal OXXX_(_!=X) descending
			}
			/*
			//first line
			if (j == 3 && i <3 && current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == 0 && current_state->board[i + 2][j - 2] == 0 && current_state->board[i+ 3][j - 3] == 0) {
			score = 250000;
			rule[1] += score;
			//       printf("2-16\n");
			//diagonal OXXX_(_!=X) descending
			}
			*/
			if (j > 2 && i < 4 && current_state->board[i][j] == 0 && current_state->board[i + 1][j - 1] == 0 && current_state->board[i + 2][j - 2] == 0 && current_state->board[i + 3][j - 3] == 1) {
				if (i > 0 && j < 5 && current_state->board[i - 1][j + 1] == 1) {
					score = 300000;
					rule[1] += score;
				} //score = 300;
				  //         if (j > 4 && i>3 && (current_state->board[i][j-1] != C4_NONE || current_state->board[i - 4][j - 5] != C4_NONE)) {
				score = 250000;
				rule[1] += score;
				//     printf("2-17\n");
				//        }
				//diagonal _XXXO(_!=X) descending
			}/*
			 //first line
			 if (j == 3 && i < 4 && current_state->board[i][j] == 0 && current_state->board[i + 1][j - 1] == 0 && current_state->board[i + 2][j - 2] == 0 && current_state->board[i + 3][j - 3] == 1) {
			 score = 250000;
			 rule[1] += score;
			 //     printf("2-17\n");
			 //diagonal _XXXO(_!=X) descending
			 }
			 */

			if (j > 2 && i < 4 && current_state->board[i][j] == 0 && current_state->board[i + 1][j - 1] == 0 && current_state->board[i + 2][j - 2] == 1 && current_state->board[i + 3][j - 3] == 0) {
				//     if (current_state->board[i - 2][j - 3] != C4_NONE) {
				score = 250000;
				rule[1] += score;
				//   printf("2-18\n");

				//      }
				//diagonal XXOX descending
			}

			if (j > 2 && i<4 && current_state->board[i][j] == 0 && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == 0 && current_state->board[i + 3][j - 3] == 0) {
				//    if (current_state->board[i - 1][j - 2] != C4_NONE) {
				score = 250000;
				rule[1] += score;
				//    printf("2-19\n");
				//  }

				//diagonal XOXX descending
			}

			/*rule 3*/ //
					   //_OOO_ (both full) horizontal
			if (i < 4 && i > 0 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 1 && current_state->board[i + 2][j] == 1 && current_state->board[i - 1][j] == C4_NONE && current_state->board[i + 3][j] == C4_NONE) {
				if (j > 0 && current_state->board[i - 1][j - 1] != C4_NONE && current_state->board[i + 3][j - 1] != C4_NONE) {
					score = 10000;
					rule[2] += score;
					//        printf("3-1\n");
				}
				else if (j == 0) {
					score = 10000;
					rule[2] += score;
				}
			}
			//_OOO_ (both full) horizontal
			//first line
			/*
			if (j == 0 && i > 0 && i < 4 && current_state->board[i][j] == 1 && current_state->board[i+1][j] == 1 && current_state->board[i+2][j] == 1 && current_state->board[i-1][j] == C4_NONE && current_state->board[i+3][j] == C4_NONE) {
			score = 10000;
			rule[2] += score;
			//      printf("3-2\n");
			}*/

			//_OOO_ (XOR full) horizontal
			if (j > 0 && i < 3 && current_state->board[i][j] == C4_NONE && current_state->board[i + 1][j] == 1 && current_state->board[i + 2][j] == 1 && current_state->board[i + 3][j] == 1 && current_state->board[i + 4][j] == C4_NONE) {
				if (current_state->board[i][j - 1] == C4_NONE && current_state->board[i + 4][j - 1] != C4_NONE) {
					score = 1000;
					rule[2] += score;
					//     printf("3-3\n");
				}
				else if (current_state->board[i][j - 1] != C4_NONE && current_state->board[i + 4][j] == C4_NONE) {
					score = 1000;
					rule[2] += score;
					//     printf("3-3\n");
				}
			}
			//_OOO_ (both empty) horizontal
			if (j > 0 && i < 3 && current_state->board[i][j] == C4_NONE && current_state->board[i + 1][j] == 1 && current_state->board[i + 2][j] == 1 && current_state->board[i + 3][j] == 1 && current_state->board[i + 4][j] == C4_NONE) {
				if (current_state->board[i][j - 1] == C4_NONE && current_state->board[i + 4][j - 1] == C4_NONE) {
					score = 2000;
					rule[2] += score;
					//        printf("3-4\n");

				}
			}

			//_OOOX horizontal
			if (i < 3 && current_state->board[i][j] == C4_NONE && current_state->board[i + 1][j] == 1 && current_state->board[i + 2][j] == 1 && current_state->board[i + 3][j] == 1 && current_state->board[i + 4][j] == 0) {
				if (j > 0 && current_state->board[i][j - 1] == C4_NONE) {
					score = 1000;
					rule[2] += score;
					//       printf("3-5\n");
				}//below empty
				else if (j > 0 && current_state->board[i][j - 1] != C4_NONE) {
					score = 300;
					rule[2] += score;
				}//below full
				else if (j == 0) { // firstline
					score = 300;
					rule[2] += score;
				}//first line
			}

			//_OOOwall horizontal
			if (i == 3 && current_state->board[i][j] == C4_NONE && current_state->board[i + 1][j] == 1 && current_state->board[i + 2][j] == 1 && current_state->board[i + 3][j] == 1) {
				if (j > 0 && current_state->board[i][j - 1] == C4_NONE) {
					score = 1000;
					rule[2] += score;
					//      printf("3-6\n");
				}
				else if (j > 0 && current_state->board[i][j - 1] != C4_NONE) {
					score = 300;
					rule[2] += score;
				}
				else if (j == 0) { // firstline
					score = 300;
					rule[2] += score;
				}

			}

			//XOOO_ horizontal
			if (i < 3 && current_state->board[i][j] == 0 && current_state->board[i + 1][j] == 1 && current_state->board[i + 2][j] == 1 && current_state->board[i + 3][j] == 1 && current_state->board[i + 4][j] == C4_NONE) {
				if (j > 0 && current_state->board[i + 4][j - 1] == C4_NONE) {
					score = 1000;
					rule[2] += score;
					//         printf("3-7\n");
				}
				else if (j > 0 && current_state->board[i + 4][j - 1] != C4_NONE) {
					score = 300;
					rule[2] += score;
				}
				else if (j == 0) { // firstline
					score = 300;
					rule[2] += score;
				}
			}

			//wallOOO_ horizontal
			if (i == 0 && i < 3 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 1 && current_state->board[i + 2][j] == 1 && current_state->board[i + 3][j] == C4_NONE) {
				if (j > 0 && current_state->board[i + 3][j - 1] == C4_NONE) {
					score = 1000;
					rule[2] += score;
					//         printf("3-8\n");
				}
				else if (j > 0 && current_state->board[i + 3][j - 1] != C4_NONE) {
					score = 300;
					rule[2] += score;
				}
				else if (j == 0) { // firstline
					score = 300;
					rule[2] += score;
				}
			}
			/*
			//_OOOX (_below full) horizontal
			if (i < 3 && j > 0 && current_state->board[i][j] == C4_NONE && current_state->board[i+1][j] == 1 && current_state->board[i+2][j] == 1 && current_state->board[i+3][j] == 1 && current_state->board[i+4][j] == 0) {
			if (current_state->board[i][j-1] != C4_NONE) {
			score = 300;
			rule[2] += score;
			//       printf("3-9\n");
			}
			}

			//_OOOX (_below full)  horizontal // first line
			if (i < 3 && j == 0 && current_state->board[i][j] == C4_NONE && current_state->board[i+1][j] == 1 && current_state->board[i+2][j] == 1 && current_state->board[i+3][j] == 1 && current_state->board[i+4][j] == 0) {
			score = 300;
			rule[2] += score;
			//    printf("3-10\n");
			}


			//_OOOwall (_below full) horizontal
			if (i == 3 && j > 0 && current_state->board[i][j] == C4_NONE && current_state->board[i+1][j] == 1 && current_state->board[i+2][j] == 1 && current_state->board[i+3][j] == 1) {
			if (current_state->board[i][j-1] != C4_NONE) {
			score = 300;
			rule[2] += score;
			//         printf("3-11\n");
			}
			}

			//_OOOwall (_below full) horizontal //first line
			if (i == 3 && j == 0 && current_state->board[i][j] == C4_NONE && current_state->board[i+1][j] == 1 && current_state->board[i+2][j] == 1 && current_state->board[i+3][j] == 1) {
			score = 300;
			rule[2] += score;
			//      printf("3-12\n");
			}

			//XOOO_ (_below full) horizontal
			if (i < 3 && j > 0 && current_state->board[i][j] == 0 && current_state->board[i+1][j] == 1 && current_state->board[i+2][j] == 1 && current_state->board[i+3][j] == 1 && current_state->board[i+4][j] == C4_NONE) {
			if (current_state->board[i+4][j-1] != C4_NONE) {
			score = 300;
			rule[2] += score;
			//     printf("3-13\n");
			}
			}

			//XOOO_ (_below full) horizontal //first line
			if (i < 3 && j == 0 && current_state->board[i][j] == 0 && current_state->board[i+1][j] == 1 && current_state->board[i+2][j] == 1 && current_state->board[i+3][j] == 1 && current_state->board[i+4][j] == C4_NONE) {
			score = 300;
			rule[2] += score;
			//      printf("3-14\n");
			}


			//wallOOO_ (_below full) horizontal
			if (i == 0 && j > 0 && current_state->board[i][j] == 1 && current_state->board[i+1][j] == 1 && current_state->board[i+2][j] == 1 && current_state->board[i+3][j] == C4_NONE) {
			if (current_state->board[i+4][j-1] != C4_NONE) {
			score = 300;
			rule[2] += score;
			//       printf("3-15\n");
			}
			}

			//wallOOO_ (_below full)  horizontal //first line
			if (i == 0 && j == 0 && current_state->board[i][j] == 1 && current_state->board[i+1][j] == 1 && current_state->board[i+2][j] == 1 && current_state->board[i+3][j] == C4_NONE) {
			score = 300;
			rule[2] += score;
			//     printf("3-16\n");
			}
			*/
			// _OOO_ (both full) diagonal ascending
			if (i > 1 && i<5 && j<4 && current_state->board[i][j] == 1 && current_state->board[i - 1][j - 1] == 1 && current_state->board[i + 1][j + 1] == 1 && current_state->board[i - 2][j - 2] == C4_NONE && current_state->board[i + 2][j + 2] == C4_NONE) {
				if (j > 2 && current_state->board[i - 2][j - 3] != C4_NONE && current_state->board[i + 2][j + 1] != C4_NONE) {
					score = 10000;
					rule[2] += score;
				}
				if (j == 2 && current_state->board[i + 2][j + 1] != C4_NONE) { //first line
					score = 10000;
					rule[2] += score;
				}
				//        printf("3-17\n");
			}
			/*
			// _OOO_ (both full) diagonal ascending //first line
			if (i > 1 && i<5 && j == 2 && j<4 && current_state->board[i][j] == 1 && current_state->board[i - 1][j - 1] == 1 && current_state->board[i + 1][j + 1] == 1 && current_state->board[i - 2][j - 2] == C4_NONE && current_state->board[i + 2][j + 2] == C4_NONE) {
			if (current_state->board[i + 2][j + 1] != C4_NONE){
			score = 10000;
			rule[2] += score;
			}
			//       printf("3-18\n");
			}*/


			//_OOO_ (XOR full) diagonal ascending
			if (i < 3 && j < 2 && current_state->board[i][j] == C4_NONE && current_state->board[i + 1][j + 1] == 1 && current_state->board[i + 2][j + 2] == 1 && current_state->board[i + 3][j + 3] == 1 && current_state->board[i + 4][j + 4] == C4_NONE) {
				if (j > 0 && current_state->board[i][j - 1] == C4_NONE && current_state->board[i + 4][j + 3] != C4_NONE) {
					score = 1000;
					rule[2] += score;
					//      printf("3-19\n");
				}
				else if (j > 0 && current_state->board[i][j - 1] != C4_NONE && current_state->board[i + 4][j + 3] == C4_NONE) {
					score = 1000;
					rule[2] += score;
					//        printf("3-19\n");
				}
				else if (j == 0 && current_state->board[i + 4][j + 3] == C4_NONE) {
					score = 1000;
					rule[2] += score;
				}
			}

			//_OOO_ (both empty) diagonal ascending
			if (j > 0 && i < 3 && j < 2 && current_state->board[i][j] == C4_NONE && current_state->board[i + 1][j + 1] == 1 && current_state->board[i + 2][j + 2] == 1 && current_state->board[i + 3][j + 3] == 1 && current_state->board[i + 4][j + 4] == C4_NONE) {
				if (current_state->board[i][j - 1] == C4_NONE && current_state->board[i + 4][j + 3] == C4_NONE) {
					score = 2000;
					rule[2] += score;
					//      printf("3-20\n");
				}
			}

			//_OOOXdiagonal ascending
			if (j > 0 && i < 3 && j < 2 && current_state->board[i][j] == C4_NONE && current_state->board[i + 1][j + 1] == 1 && current_state->board[i + 2][j + 2] == 1 && current_state->board[i + 3][j + 3] == 1 && current_state->board[i + 4][j + 4] == 0) {
				if (current_state->board[i][j - 1] == C4_NONE) {
					score = 1000;
					rule[2] += score;
					//       printf("3-21\n");
				}
				if (current_state->board[i][j - 1] != C4_NONE) {
					score = 300;
					rule[2] += score;
					//      printf("3-25\n");
				}
			}

			//_OOOwall diagonal ascending
			if (j > 0 && i == 3 && j < 3 && current_state->board[i][j] == C4_NONE && current_state->board[i + 1][j + 1] == 1 && current_state->board[i + 2][j + 2] == 1 && current_state->board[i + 3][j + 3] == 1) {
				if (current_state->board[i][j - 1] == C4_NONE) {
					score = 1000;
					rule[2] += score;
					//          printf("3-22\n");
				}
				if (current_state->board[i][j - 1] != C4_NONE) {
					score = 300;
					rule[2] += score;
					//      printf("3-25\n");
				}
			}

			//XOOO_  diagonal ascending
			if (i < 3 && j < 2 && current_state->board[i][j] == 0 && current_state->board[i + 1][j + 1] == 1 && current_state->board[i + 2][j + 2] == 1 && current_state->board[i + 3][j + 3] == 1 && current_state->board[i + 4][j + 4] == C4_NONE) {
				if (current_state->board[i + 4][j + 3] == C4_NONE) {
					score = 1000;
					rule[2] += score;
					//    printf("3-23\n");
				}
				if (current_state->board[i + 4][j + 3] != C4_NONE) {
					score = 300;
					rule[2] += score;
					//      printf("3-25\n");
				}
			}

			//wallOOO_ diagonal ascending
			if (i == 0 && j < 4 && current_state->board[i][j] == 1 && current_state->board[i + 1][j + 1] == 1 && current_state->board[i + 2][j + 2] == 1 && current_state->board[i + 3][j + 3] == C4_NONE) {
				if (current_state->board[i + 3][j + 2] == C4_NONE) {
					score = 1000;
					rule[2] += score;
					//    printf("3-24\n");
				}
				if (current_state->board[i + 3][j + 2] != C4_NONE) {
					score = 300;
					rule[2] += score;
					//      printf("3-25\n");
				}
			}
			/*
			//_OOOX (_below full) diagonal ascending
			if (j > 0 && i < 3 && j < 2 && current_state->board[i][j] == C4_NONE && current_state->board[i+1][j+1] == 1 && current_state->board[i+2][j+2] == 1 && current_state->board[i+3][j+3] == 1 && current_state->board[i+4][j+4] == 0) {
			if (current_state->board[i][j-1] != C4_NONE) {
			score = 300;
			rule[2] += score;
			//      printf("3-25\n");
			}
			}

			//_OOOwall (_below full) diagonal ascending
			if (j > 0 && i == 3 && j < 3 && current_state->board[i][j] == C4_NONE && current_state->board[i+1][j+1] == 1 && current_state->board[i+2][j+2] == 1 && current_state->board[i+3][j+3] == 1) {
			if (current_state->board[i][j-1] != C4_NONE) {
			score = 300;
			rule[2] += score;
			//          printf("3-26\n");
			}
			}

			//XOOO_ (_below full) diagonal ascending
			if (i < 3 && j < 2 && current_state->board[i][j] == 0 && current_state->board[i+1][j+1] == 1 && current_state->board[i+2][j+2] == 1 && current_state->board[i+3][j+3] == 1 && current_state->board[i+4][j+4] == C4_NONE) {
			if (current_state->board[i+4][j+3] != C4_NONE) {
			score = 300;
			rule[2] += score;
			//           printf("3-27\n");
			}
			}

			//wallOOO_ (_below full) diagonal ascending
			if (i == 0 && j < 4 && current_state->board[i][j] == 1 && current_state->board[i+1][j+1] == 1 && current_state->board[i+2][j+2] == 1 && current_state->board[i+3][j+3] == C4_NONE) {
			if (current_state->board[i+3][j+2] != C4_NONE) {
			score = 300;
			rule[2] += score;
			//          printf("3-28\n");
			}
			}
			*/
			// _OOO_ (both full) diagonal descending
			if (i>1 && i<5 && j<4 && current_state->board[i - 1][j + 1] == 1 && current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == C4_NONE && current_state->board[i - 2][j + 2] == C4_NONE) {
				if (j > 2 && current_state->board[i + 2][j - 3] != C4_NONE && current_state->board[i - 2][j + 1] != C4_NONE) {
					score = 10000;
					rule[2] += score;
				}
				//     printf("3-29\n");
				if (j == 2 && current_state->board[i - 2][j + 1] != C4_NONE) { // first line
					score = 10000;
					rule[2] += score;
				}
			}
			/*
			// _OOO_ (both full) diagonal descending //first line
			if (i>1 && i<5 && j == 2 && current_state->board[i - 1][j + 1] == 1 && current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == C4_NONE && current_state->board[i - 2][j + 2] == C4_NONE) {
			if (current_state->board[i - 2][j + 1] != C4_NONE){
			score = 10000;
			rule[2] += score;
			}
			//        printf("3-30\n");
			}
			*/

			//_OOO_ (XOR full) diagonal descending
			if (j > 3 && i < 3 && current_state->board[i][j] == C4_NONE && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == 1 && current_state->board[i + 3][j - 3] == 1 && current_state->board[i + 4][j - 4] == C4_NONE) {
				if (j > 5 && current_state->board[i][j - 1] == C4_NONE && current_state->board[i + 4][j - 5] != C4_NONE) {
					score = 1000;
					rule[2] += score;
					//       printf("3-31\n");
				}
				else if (j > 5 && current_state->board[i][j - 1] != C4_NONE && current_state->board[i + 4][j - 5] == C4_NONE) {
					score = 1000;
					rule[2] += score;
					//        printf("3-31\n");
				}
				else if (j == 5 && current_state->board[i][j - 1] == C4_NONE) {
					score = 1000;
					rule[2] += score;
				}
			}
			//_OOO_ (both emtpy) diagonal descending
			if (j > 4 && i < 3 && current_state->board[i][j] == C4_NONE && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == 1 && current_state->board[i + 3][j - 3] == 1 && current_state->board[i + 4][j - 4] == C4_NONE) {
				if (current_state->board[i][j - 1] == C4_NONE && current_state->board[i + 4][j - 5] == C4_NONE) {
					score = 2000;
					rule[2] += score;
					//         printf("3-32\n");
				}
			}

			//_OOOX  diagonal descending
			if (j > 3 && i < 3 && current_state->board[i][j] == C4_NONE && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == 1 && current_state->board[i + 3][j - 3] == 1 && current_state->board[i + 4][j - 4] == 0) {
				if (current_state->board[i][j - 1] == C4_NONE) {
					score = 1000;
					rule[2] += score;
					//        printf("3-33\n");
				}
			}

			//_OOOwall diagonal descending
			if (i == 3 && j > 2 && current_state->board[i][j] == C4_NONE && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == 1 && current_state->board[i + 3][j - 3] == 1) {
				if (current_state->board[i][j - 1] == C4_NONE) {
					score = 1000;
					rule[2] += score;
					//        printf("3-34\n");
				}
			}

			//XOOO_ diagonal descending
			if (j > 4 && i < 3 && current_state->board[i][j] == 0 && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == 1 && current_state->board[i + 3][j - 3] == 1 && current_state->board[i + 4][j - 4] == C4_NONE) {
				if (current_state->board[i + 4][j - 5] == C4_NONE) {
					score = 1000;
					rule[2] += score;
					//      printf("3-35\n");
				}
			}

			//wallOOO_  diagonal descending
			if (j > 3 && i == 0 && current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == 1 && current_state->board[i + 3][j - 3] == C4_NONE) {
				if (current_state->board[i + 3][j - 4] == C4_NONE) {
					score = 1000;
					rule[2] += score;
					//      printf("3-36\n");
				}
			}

			//_OOOX (_below full) diagonal descending
			if (j > 3 && i < 3 && current_state->board[i][j] == C4_NONE && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == 1 && current_state->board[i + 3][j - 3] == 1 && current_state->board[i + 4][j - 4] == 0) {
				if (current_state->board[i][j - 1] != C4_NONE) {
					score = 300;
					rule[2] += score;
					//        printf("3-37\n");
				}
			}

			//_OOOwall (_below full) diagonal descending
			if (j > 2 && i == 3 && current_state->board[i][j] == C4_NONE && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == 1 && current_state->board[i + 3][j - 3] == 1) {
				if (current_state->board[i][j - 1] != C4_NONE) {
					score = 300;
					rule[2] += score;
					//         printf("3-38\n");
				}
			}

			//XOOO_ (_below full) diagonal descending
			if (j > 3 && i < 3 && current_state->board[i][j] == 0 && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == 1 && current_state->board[i + 3][j - 3] == 1 && current_state->board[i + 4][j - 4] == C4_NONE) {
				if (j > 4 && current_state->board[i + 4][j - 5] != C4_NONE) {
					score = 300;
					rule[2] += score;
					//     printf("3-35\n");
				}
				if (j == 4) {
					score = 300;
					rule[2] += score;
				}
			}

			//wallOOO_ (_below full) diagonal descending
			if (j > 2 && i == 0 && current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == 1 && current_state->board[i + 3][j - 3] == C4_NONE) {
				if (j > 3 && current_state->board[i + 3][j - 4] != C4_NONE) {
					score = 300;
					rule[2] += score;
					//          printf("3-36\n");
				}
				if (j == 3) {
					score = 300;
					rule[2] += score;
				}
			}
			// XOOOX horizontal
			if (i < 3 && current_state->board[i][j] == 0 && current_state->board[i + 1][j] == 1 && current_state->board[i + 2][j] == 1 && current_state->board[i + 3][j] == 1 && current_state->board[i + 4][j] == 0) {
				score = -200;
				rule[2] += score;
			}
			//wal000X 
			if (i ==0 &&current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 1 && current_state->board[i + 2][j] == 1 && current_state->board[i + 3][j] == 0) {
				score = -200;
				rule[2] += score;
			}
			//X000wall
			if (i ==3 && current_state->board[i][j] == 0 && current_state->board[i + 1][j] == 1 && current_state->board[i + 2][j] == 1 && current_state->board[i + 3][j] == 1) {
				score = -200;
				rule[2] += score;
			}
			// XOOOX diagonal ascending
			if (i < 3 && j < 2 && current_state->board[i][j] == 0 && current_state->board[i + 1][j + 1] == 1 && current_state->board[i + 2][j + 2] == 1 && current_state->board[i + 3][j + 3] == 1 && current_state->board[i + 4][j + 4] == 0) {
				score = -200;
				rule[2] += score;
			}
			//wall000X   /
			if (i==0&&j < 3 && current_state->board[i][j] == 1 && current_state->board[i + 1][j + 1] == 1 && current_state->board[i + 2][j + 2] == 1 && current_state->board[i + 3][j + 3] == 0) {
				score = -200;
				rule[2] += score;
			}
			//X000wall    /
			if (i == 3 && j < 3 && current_state->board[i][j] == 0 && current_state->board[i + 1][j + 1] == 1 && current_state->board[i + 2][j + 2] == 1 && current_state->board[i + 3][j + 3] == 1) {
				score = -200;
				rule[2] += score;
			}

			// XOOOX diagonal descending
			if (i < 3 && j > 3 && current_state->board[i][j] == 0 && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == 1 && current_state->board[i + 3][j - 3] == 1 && current_state->board[i + 4][j - 4] == 0) {
				score = -200;
				rule[2] += score;
			}
			//wall000X \ descending 

			if (i ==0 && j > 2 && current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == 1 && current_state->board[i + 3][j - 3] == 0) {
				score = -200;
				rule[2] += score;
			}
			//X000wall \ descending

		    if (i ==3 && j > 2 && current_state->board[i][j] == 0 && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == 1 && current_state->board[i + 3][j - 3] == 1) {
			score = -200;
			rule[2] += score;
			}


			/*rule 4*/ // Human 이 양 끝이 비어 있는 3개 돌이 될 가능성이 있으면 막는다.
					   //**가로**//
					   //_XX_ -> _XXO_
			if (i > 0 && i<4 && current_state->board[i][j] == 0 && current_state->board[i + 1][j] == 0 && current_state->board[i + 2][j] == 1 && current_state->board[i - 1][j] == C4_NONE && current_state->board[i + 3][j] == C4_NONE) {
				if (j > 0 && current_state->board[i - 1][j - 1] != C4_NONE && current_state->board[i + 3][j - 1] != C4_NONE) {
					score = 5000;
					rule[3] += score;
				}
				else if (j > 0 && current_state->board[i - 1][j - 1] == C4_NONE && current_state->board[i + 3][j - 1] != C4_NONE) {
					score = 150;
					rule[3] += score;
				}
				else if (j > 0 && current_state->board[i - 1][j - 1] != C4_NONE && current_state->board[i + 3][j - 1] == C4_NONE) {
					score = 150;
					rule[3] += score;
				}

				else if (j == 0) {
					score = 5000;
					rule[3] += score;
				}
				//    printf("4-1\n");
			}
			//첫줄
			/*
			if (j == 0 && i > 0 && i<4 && current_state->board[i][j] == 0 && current_state->board[i + 1][j] == 0 && current_state->board[i + 2][j] == 1 && current_state->board[i - 1][j] == C4_NONE && current_state->board[i + 3][j] == C4_NONE) {
			score = 5000;
			rule[3] += score;
			//   printf("4-2\n");
			}*/

			//OXX
			if (i > 0 && i<4 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 0 && current_state->board[i + 2][j] == 0 && current_state->board[i - 1][j] == C4_NONE && current_state->board[i + 3][j] == C4_NONE) {
				if (j > 0 && current_state->board[i - 1][j - 1] != C4_NONE && current_state->board[i + 3][j - 1] != C4_NONE) {
					score = 5000;
					rule[3] += score;
				}
				else if (j > 0 && current_state->board[i - 1][j - 1] == C4_NONE && current_state->board[i + 3][j - 1] != C4_NONE) {
					score = 150;
					rule[3] += score;
				}
				else if (j > 0 && current_state->board[i - 1][j - 1] != C4_NONE && current_state->board[i + 3][j - 1] == C4_NONE) {
					score = 150;
					rule[3] += score;
				}
				else if (j == 0) {
					score = 5000;
					rule[3] += score;
				}
				//   printf("4-3\n");
			}
			//첫줄
			/*
			if (j == 0 && i > 0 && i<4 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 0 && current_state->board[i + 2][j] == 0 && current_state->board[i - 1][j] == C4_NONE && current_state->board[i + 3][j] == C4_NONE) {
			score = 5000;
			rule[3] += score;
			}*/

			//XOX
			if (i > 0 && i<4 && current_state->board[i][j] == 0 && current_state->board[i + 1][j] == 1 && current_state->board[i + 2][j] == 0 && current_state->board[i - 1][j] == C4_NONE && current_state->board[i + 3][j] == C4_NONE) {
				if (j > 0 && current_state->board[i - 1][j - 1] != C4_NONE && current_state->board[i + 3][j - 1] != C4_NONE) {
					score = 5000;
					rule[3] += score;
				}
				else if (j > 0 && (current_state->board[i - 1][j - 1] != C4_NONE || current_state->board[i + 3][j - 1] != C4_NONE)) {
					score = 150;
					rule[3] += score;
				}
				//       printf("4-5\n");
				else if (j == 0) {
					score = 5000;
					rule[3] += score;
				}
			}

			//첫줄
			/*
			if (j == 0 && i > 0 && i<4 && current_state->board[i][j] == 0 && current_state->board[i + 1][j] == 1 && current_state->board[i + 2][j] == 0 && current_state->board[i - 1][j] == C4_NONE && current_state->board[i + 3][j] == C4_NONE) {
			score = 5000;
			rule[3] += score;
			//     printf("4-6\n");
			}*/

			//**대각선/**//
			//XXO
			if (j<4 && i>1 && i<5 && current_state->board[i][j] == 0 && current_state->board[i - 1][j - 1] == 0 && current_state->board[i + 1][j + 1] == 1 && current_state->board[i - 2][j - 2] == C4_NONE && current_state->board[i + 2][j + 2] == C4_NONE) {
				if (j>2 && current_state->board[i - 2][j - 3] != C4_NONE && current_state->board[i + 2][j + 1] != C4_NONE) {
					score = 5000;
					//      rule[3] += score;
				}
				else if (j>2 && (current_state->board[i - 2][j - 3] != C4_NONE || current_state->board[i + 2][j + 1] != C4_NONE)) {
					score = 150;
					rule[3] += score;
				}
				//   printf("4-7\n");
				else if (j == 2 && current_state->board[i + 2][j + 1] != C4_NONE) {
					score = 5000;
					rule[3] += score;
				}
				else if (j == 2 && current_state->board[i + 2][j + 1] == C4_NONE) {
					score = 150;
					rule[3] += score;
				}
			}
			//OXX
			if (j<4 && i>1 && i<5 && current_state->board[i][j] == 0 && current_state->board[i - 1][j - 1] == 1 && current_state->board[i + 1][j + 1] == 0 && current_state->board[i - 2][j - 2] == C4_NONE && current_state->board[i + 2][j + 2] == C4_NONE) {
				if (j > 2 && current_state->board[i - 2][j - 3] != C4_NONE && current_state->board[i + 2][j + 1] != C4_NONE) {
					score = 5000;
					rule[3] += score;
				}
				else if (j > 2 && (current_state->board[i - 2][j - 3] != C4_NONE || current_state->board[i + 2][j + 1] != C4_NONE)) {
					score = 150;
					rule[3] += score;
				}
				//  printf("4-8\n");
				else if (j == 2 && current_state->board[i + 2][j + 1] != C4_NONE) {
					score = 5000;
					rule[3] += score;
				}
				else if (j == 2 && current_state->board[i + 2][j + 1] == C4_NONE) {
					score = 150;
					rule[3] += score;
				}

			}
			//XOX
			if (j<4 && i>1 && i<5 && current_state->board[i][j] == 1 && current_state->board[i - 1][j - 1] == 0 && current_state->board[i + 1][j + 1] == 0 && current_state->board[i - 2][j - 2] == C4_NONE && current_state->board[i + 2][j + 2] == C4_NONE) {
				if (j>2 && current_state->board[i - 2][j - 3] != C4_NONE && current_state->board[i + 2][j + 1] != C4_NONE) {
					score = 5000;
					rule[3] += score;
				}
				else if (j>2 && (current_state->board[i - 2][j - 3] != C4_NONE || current_state->board[i + 2][j + 1] != C4_NONE)) {
					score = 150;
					rule[3] += score;
				}
				//   printf("4-9\n");
				else if (j == 2 && current_state->board[i + 2][j + 1] != C4_NONE) {
					score = 5000;
					rule[3] += score;
				}
				else if (j == 2 && current_state->board[i + 2][j + 1] == C4_NONE) {
					score = 150;
					rule[3] += score;
				}


			}
			//**대각선 \ **//
			//XXO
			if (i>1 && j<4 && i<5 && current_state->board[i - 1][j + 1] == 0 && current_state->board[i][j] == 0 && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == C4_NONE && current_state->board[i - 2][j + 2] == C4_NONE) {
				if (j>2 && current_state->board[i + 2][j - 3] != C4_NONE && current_state->board[i - 2][j + 1] != C4_NONE) {
					score = 5000;
					rule[3] += score;
				}
				else if (j>2 && (current_state->board[i + 2][j - 3] != C4_NONE || current_state->board[i - 2][j + 1] != C4_NONE)) {
					score = 150;
					rule[3] += score;
				}
				else if (j == 2 && current_state->board[i - 2][j + 1] != C4_NONE) {
					score = 5000;
					rule[3] += score;
				}
				else if (j == 2 && current_state->board[i - 2][j + 1] == C4_NONE) {
					score = 150;
					rule[3] += score;
				}

			}
			//OXX
			if (i>1 && j<4 && i<5 && current_state->board[i - 1][j + 1] == 1 && current_state->board[i][j] == 0 && current_state->board[i + 1][j - 1] == 0 && current_state->board[i + 2][j - 2] == C4_NONE && current_state->board[i - 2][j + 2] == C4_NONE) {
				if (j>2 && current_state->board[i + 2][j - 3] != C4_NONE && current_state->board[i - 2][j + 1] != C4_NONE) {
					score = 5000;
					rule[3] += score;
				}
				else if (j>2 && (current_state->board[i + 2][j - 3] != C4_NONE || current_state->board[i - 2][j + 1] != C4_NONE)) {
					score = 150;
					rule[3] += score;
				}
				//   printf("4-10\n");
				else if (j == 2 && current_state->board[i - 2][j + 1] != C4_NONE) {
					score = 5000;
					rule[3] += score;
				}
				else if (j == 2 && current_state->board[i - 2][j + 1] == C4_NONE) {
					score = 150;
					rule[3] += score;
				}
			}
			//XOX
			if (i>1 && j<4 && i<5 && current_state->board[i - 1][j + 1] == 0 && current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == 0 && current_state->board[i + 2][j - 2] == C4_NONE && current_state->board[i - 2][j + 2] == C4_NONE) {
				if (j>2 && current_state->board[i + 2][j - 3] != C4_NONE && current_state->board[i - 2][j + 1] != C4_NONE) {
					score = 5000;
					rule[3] += score;
				}
				else if (j>2 && (current_state->board[i + 2][j - 3] != C4_NONE || current_state->board[i - 2][j + 1] != C4_NONE)) {
					score = 150;
					rule[3] += score;
				}
				//      printf("4-11\n");
				else if (j == 2 && current_state->board[i - 2][j + 1] != C4_NONE) {
					score = 5000;
					rule[3] += score;
				}
				else if (j == 2 && current_state->board[i - 2][j + 1] == C4_NONE) {
					score = 150;
					rule[3] += score;
				}

			}

			/*rule 5*/ //7자 모양
			if (i>1 && j>1 && current_state->board[i][j] == 1 && current_state->board[i - 1][j] == 1 && current_state->board[i - 2][j] == 1 && current_state->board[i - 1][j - 1] == 1 && current_state->board[i - 2][j - 2] == 1) {

				if (i>2 && i < 6 && j < 5 && current_state->board[i + 1][j + 1] == 0 && current_state->board[i - 3][j] == 0) {//4개 만들 가능성이 막혀 있으면 점수 주지 마라!
					score = -100;
					rule[4] += score;
					//    printf("5-1\n");
				}
				else {
					score = 2000;
					rule[4] += score;
					//  printf("5-1\n");
				}
				//내가 7만들수 있는거 // 7
			}
			if (j>1 && i<5 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 1 && current_state->board[i + 2][j] == 1 && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == 1) {
				if (i>0 && i<4 && j<5 && current_state->board[i - 1][j + 1] == 0 && current_state->board[i + 3][j] == 0) {
					score = -100;
					rule[4] += score;
					//    printf("5-2\n");
				}
				else {
					score = 2000;
					rule[4] += score;
					//    printf("5-2\n");
				}
				//좌우반전 7

			}
			if (i<5 && j<4 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 1 && current_state->board[i + 2][j] == 1 && current_state->board[i + 1][j + 1] == 1 && current_state->board[i + 2][j + 2] == 1) {
				//좌우 상하 반전 7
				if (i>0 && i<4 && j<3 && current_state->board[i - 1][j] == 0 && current_state->board[i + 3][j + 3] == 0) {
					score = -100;
					rule[4] += score;
					//     printf("5-3\n");
				}
				else {
					score = 2000;
					rule[4] += score;
					//     printf("5-3\n");
				}

			}
			if (i>1 && j<5 && current_state->board[i][j] == 1 && current_state->board[i - 1][j] == 1 && current_state->board[i - 2][j] == 1 && current_state->board[i - 1][j + 1] == 1 && current_state->board[i - 2][j + 2] == 1) {
				//상하반전 7
				if (i<6 && i>2 && j<3 && current_state->board[i + 1][j] == 0 && current_state->board[i - 3][j + 3] == 0) {
					score = -100;
					rule[4] += score;
					//   printf("5-4\n");
				}
				else {
					score = 2000;
					rule[4] += score;
					//    printf("5-4\n");
				}
			}
			if (i>1 && j>1 && current_state->board[i][j] == 1 && current_state->board[i - 1][j] == 0 && current_state->board[i - 2][j] == 0 && current_state->board[i - 1][j - 1] == 0 && current_state->board[i - 2][j - 2] == 0) {
				//score =음수음수 상대방 7 가능성을 ai가 막는거
				if (i>2 && i < 6 && j < 5 && current_state->board[i + 1][j + 1] == 0 && current_state->board[i - 3][j] == 0) {//상대방의 4개 만들 가능성이 막혀 있으면(옆이 빈칸이 아니면) 점수 주지 마라!
					score = -100;
					rule[4] += score;
					//     printf("5-5\n");
				}
				else {
					score = 2000;
					rule[4] += score;
					//      printf("5-5\n");
				}

			}
			if (j>1 && i<5 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 0 && current_state->board[i + 2][j] == 0 && current_state->board[i + 1][j - 1] == 0 && current_state->board[i + 2][j - 2] == 0) {
				if (i>0 && i<4 && j<5 && current_state->board[i - 1][j + 1] == 0 && current_state->board[i + 3][j] == 0) {
					score = -100;
					rule[4] += score;
					//   printf("5-6\n");
				}
				else {
					score = 2000;
					rule[4] += score;
					//        printf("5-6\n");
				}

			}
			if (i<5 && j<4 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 0 && current_state->board[i + 2][j] == 0 && current_state->board[i + 1][j + 1] == 0 && current_state->board[i + 2][j + 2] == 0) {
				//좌우 상하 반전 7
				if (i>0 && i<4 && j<3 && current_state->board[i - 1][j] == 0 && current_state->board[i + 3][j + 3] == 0) {
					score = -100;
					rule[4] += score;
					//     printf("5-7\n");
				}
				else {
					score = 2000;
					rule[4] += score;
					//   printf("5-7\n");
				}

			}
			if (i>1 && j<4 && current_state->board[i][j] == 1 && current_state->board[i - 1][j] == 0 && current_state->board[i - 2][j] == 0 && current_state->board[i - 1][j + 1] == 0 && current_state->board[i - 2][j + 2] == 0) {
				//상하반전 7
				if (i<6 && i>2 && j<3 && current_state->board[i + 1][j] == 0 && current_state->board[i - 3][j + 3] == 0) {
					score = -100;
					rule[4] += score;
					//    printf("5-8\n");
				}
				else {
					score = 2000;
					rule[4] += score;
					//    printf("5-8\n");
				}

			}
			/*rule6*/ //다음에 두면 진다

			if (j<5 && i>2 && current_state->board[i - 3][j + 1] == 0 && current_state->board[i - 2][j + 1] == 0 && current_state->board[i - 1][j + 1] == 0 && current_state->board[i][j] == 1 && current_state->board[i][j + 1] == C4_NONE) {//xxx_ horizontal
				score = -10000;
				rule[5] += score;
				//    printf("6-1\n");
			}
			if (i<4 && j<5 && current_state->board[i + 1][j + 1] == 0 && current_state->board[i + 2][j + 1] == 0 && current_state->board[i + 3][j + 1] == 0 && current_state->board[i][j] == 1 && current_state->board[i][j + 1] == C4_NONE) {//_xxx
				score = -10000;
				rule[5] += score;
				// printf("6-2\n");
			}
			if (j<5 && i>0 && i<5 && current_state->board[i - 1][j + 1] == 0 && current_state->board[i][j] == 1 && current_state->board[i + 1][j + 1] == 0 && current_state->board[i + 2][j + 1] == 0 && current_state->board[i][j + 1] == C4_NONE) {//x_xx
				score = -10000;
				rule[5] += score;
				//    printf("6-3\n");
			}
			if (j<5 && i>1 && i<6 && current_state->board[i - 2][j + 1] == 0 && current_state->board[i - 1][j + 1] == 0 && current_state->board[i][j] == 1 && current_state->board[i + 1][j + 1] == 0 && current_state->board[i][j + 1] == C4_NONE) {//xx_x
				score = -10000;
				rule[5] += score;
				//   printf("6-4\n");
			}
			if (j<2 && i>2 && current_state->board[i - 3][j + 4] == 0 && current_state->board[i - 2][j + 3] == 0 && current_state->board[i - 1][j + 2] == 0 && current_state->board[i][j] == 1 && current_state->board[i][j + 1] == C4_NONE) {//xxx_ diagonal descending
				score = -10000;
				rule[5] += score;
				//      printf("6-5\n");
			}
			if (j>1 && i<4 && current_state->board[i + 1][j] == 0 && current_state->board[i + 2][j - 1] == 0 && current_state->board[i + 3][j - 2] == 0 && current_state->board[i][j] == 1 && current_state->board[i][j + 1] == C4_NONE) {//_xxx diagonal descending
				score = -10000;
				rule[5] += score;
				//   printf("6-6\n");
			}
			if (j>0 && i>0 && j<4 && i<5 && current_state->board[i - 1][j + 2] == 0 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 0 && current_state->board[i + 2][j - 1] == 0 && current_state->board[i][j + 1] == C4_NONE) {//x_xx diagonal descending
				score = -10000;
				rule[5] += score;
				//   printf("6-7\n");
			}
			if (i>1 && j<3 && i<6 && current_state->board[i - 2][j + 3] == 0 && current_state->board[i - 1][j + 2] == 0 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 0 && current_state->board[i][j + 1] == C4_NONE) {//xx_x diagonal descending
				score = -10000;
				rule[5] += score;
				//    printf("6-8\n");
			}
			if (j<2 && i<4 && current_state->board[i + 1][j + 2] == 0 && current_state->board[i + 2][j + 3] == 0 && current_state->board[i + 3][j + 4] == 0 && current_state->board[i][j] == 1 && current_state->board[i][j + 1] == C4_NONE) {//_xxx diagonal ascending
				score = -10000;
				rule[5] += score;
				//   printf("6-9\n");
			}
			if (j < 5 && j>1 && i>2 && current_state->board[i - 3][j - 2] == 0 && current_state->board[i - 2][j - 1] == 0 && current_state->board[i - 1][j] == 0 && current_state->board[i][j] == 1 && current_state->board[i][j + 1] == C4_NONE) {//xxx_ diagonal ascending
				score = -10000;
				rule[5] += score;
				//     printf("6-10\n");
			}
			if (i>0 && j<3 && i<5 && current_state->board[i - 1][j] == 0 && current_state->board[i][j] == 1 && current_state->board[i + 1][j + 2] == 0 && current_state->board[i + 2][j + 3] == 0 && current_state->board[i][j + 1] == C4_NONE) {//x_xx diagonal ascending
				score = -10000;
				rule[5] += score;
				//  printf("6-11\n");
			}
			if (j>0 && i>1 && j<4 && i<6 && current_state->board[i - 2][j - 1] == 0 && current_state->board[i - 1][j] == 0 && current_state->board[i][j] == 1 && current_state->board[i + 1][j + 2] == 0 && current_state->board[i][j + 1] == C4_NONE) {//xx_x diagonal ascending
				score = -10000;
				rule[5] += score;
				//      printf("6-12\n");
			}
			/*
			/*rule7 //7.내 차례 시에 나에게 유리하게 하도록 만든 룰이다. 내 차례 일 때 나의 돌이 2개 연결되어 있는 상황이라면 이를 이용해 나의 돌을 3개로 연결시킨다
			//_ooo || ooo_ 이렇게 생각. _의 밑에 가 비어 있는 경우
			if (i>0 && i<5 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 1 && current_state->board[i + 2][j] == 1) {//horizontal _ooo || ooo_
			if ((j>0 && current_state->board[i - 1][j - 1] == C4_NONE) || (i<4 && current_state->board[i + 3][j - 1] == C4_NONE)) {
			score = 10;
			total += score;
			}
			printf("7-1\n");
			}
			else if (i<5 && j<4 && current_state->board[i][j] == 1 && current_state->board[i + 1][j + 1] == 1 && current_state->board[i + 2][j + 2] == 1) {//diagonal ascending _ooo || ooo_
			if ((j>1 && i>0 && current_state->board[i - 1][j - 2] == C4_NONE) || (i<4 && current_state->board[i + 3][j + 2] == C4_NONE)) {
			score = 10;
			total += score;
			}
			printf("7-2\n");
			}
			else if (j>1 && i<5 && current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == 1) {//diagonal descending _ooo || ooo_
			if ((i>0 && current_state->board[i - 1][j] == C4_NONE) || (j>3 && i<4 && current_state->board[i + 3][j - 4] == C4_NONE)) {
			score = 10;
			total += score;
			}
			printf("7-3\n");

			}
			else if (j > 1 && current_state->board[i][j] == 1 && current_state->board[i][j - 1] == 0 && current_state->board[i][j - 2] == 0) {
			score = 5;
			total += score;
			printf("7-4\n");
			}
			*/

			/*
			/*rule7 //7.내 차례 시에 나에게 유리하게 하도록 만든 룰이다. 내 차례 일 때 나의 돌이 2개 연결되어 있는 상황이라면 이를 이용해 나의 돌을 3개로 연결시킨다
			//_ooo || ooo_ 이렇게 생각. _의 밑에 가 비어 있는 경우
			if (i>0 && i<5 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 1 && current_state->board[i + 2][j] == 1) {//horizontal _ooo || ooo_
			if ((j>0 && current_state->board[i - 1][j - 1] == C4_NONE) || (i<4 && current_state->board[i + 3][j - 1] == C4_NONE)) {
			score = 10;
			total += score;
			}
			printf("7-1\n");
			}
			else if (i<5 && j<4 && current_state->board[i][j] == 1 && current_state->board[i + 1][j + 1] == 1 && current_state->board[i + 2][j + 2] == 1) {//diagonal ascending _ooo || ooo_
			if ((j>1 && i>0 && current_state->board[i - 1][j - 2] == C4_NONE) || (i<4 && current_state->board[i + 3][j + 2] == C4_NONE)) {
			score = 10;
			total += score;
			}
			printf("7-2\n");
			}
			else if (j>1 && i<5 && current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == 1) {//diagonal descending _ooo || ooo_
			if ((i>0 && current_state->board[i - 1][j] == C4_NONE) || (j>3 && i<4 && current_state->board[i + 3][j - 4] == C4_NONE)) {
			score = 10;
			total += score;
			}
			printf("7-3\n");

			}
			else if (j > 1 && current_state->board[i][j] == 1 && current_state->board[i][j - 1] == 0 && current_state->board[i][j - 2] == 0) {
			score = 5;
			total += score;
			printf("7-4\n");
			}
			*/

			// rule 7//
			// **두면 한개되는거**//
			//1. 00_0_00 가로 한칸띄워서 양쪽으로 ai 돌 2개
			if (i < 4 && i > 2 && current_state->board[i][j] == 1 && current_state->board[i - 2][j] == 1 && current_state->board[i + 2][j] == 1 && current_state->board[i - 3][j] == 1 && current_state->board[i + 3][j] == 1 && current_state->board[i - 1][j] == C4_NONE && current_state->board[i + 1][j] == C4_NONE) {
				if (j > 0 && current_state->board[i - 1][j - 1] != C4_NONE && current_state->board[i + 1][j - 1] != C4_NONE) {
					score = 10000;
					rule[6] += score;
				} //양쪽 받침 있다.

				else if (j == 0) { // first line
					score = 10000;
					rule[6] += score;
				}

				else if (j > 0 && (current_state->board[i - 1][j - 1] == C4_NONE && current_state->board[i + 1][j - 1] == C4_NONE)) {
					score = 1000;
					rule[6] += score;
				} //양쪽받침없다
				else if (j > 0 && (current_state->board[i - 1][j - 1] != C4_NONE || current_state->board[i + 1][j - 1] != C4_NONE)) {
					score = 500;
					rule[6] += score;
				} //한쪽받침있다

			}

			//2. 0_0_0 가로  한칸띄워서 양쪽으로 AI 돌 한개
			if (i < 5 && i>1 && current_state->board[i][j] == 1 && current_state->board[i - 2][j] == 1 && current_state->board[i + 2][j] == 1 && current_state->board[i - 1][j] == C4_NONE && current_state->board[i + 1][j] == C4_NONE) {
				if (j > 0 && current_state->board[i - 1][j - 1] != C4_NONE && current_state->board[i + 1][j - 1] != C4_NONE) {
					score = 200;
					rule[6] += score;
				} //양쪽 받침 있다.
				if (j == 0) {
					score = 200;
					rule[6] += score;
				}
				else if (j > 0 && (current_state->board[i - 1][j - 1] == C4_NONE && current_state->board[i + 1][j - 1] == C4_NONE)) {
					score = 150;
					rule[6] += score;
				} //양쪽받침없다
				else if (j > 0 && (current_state->board[i - 1][j - 1] != C4_NONE || current_state->board[i + 1][j - 1] != C4_NONE)) {
					score = 100;
					rule[6] += score;
				} //한쪽받침있다

			}/*
			 //first line
			 if (i < 5 && i>1 && j == 0 && current_state->board[i][j] == 1 && current_state->board[i - 2][j] == 1 && current_state->board[i + 2][j] == 1 && current_state->board[i - 1][j] == C4_NONE && current_state->board[i + 1][j] == C4_NONE) {
			 score = 200;
			 rule[6] += score;
			 }
			 */

			 //2. /
			if (i < 5 && i>1 && j < 4 && j>1 && current_state->board[i][j] == 1 && current_state->board[i - 2][j - 2] == 1 && current_state->board[i + 2][j + 2] == 1 && current_state->board[i - 1][j - 1] == C4_NONE && current_state->board[i + 1][j + 1] == C4_NONE) {
				if (current_state->board[i - 1][j - 2] != C4_NONE && current_state->board[i + 1][j] != C4_NONE) {
					score = 200;
					rule[6] += score;
				}//양쪽 받침 ㅇ
				else if (current_state->board[i - 1][j - 2] == C4_NONE && current_state->board[i + 1][j] == C4_NONE) {
					score = 150;
					rule[6] += score;
				}//양쪽 받침 x
				else if (current_state->board[i - 1][j - 2] != C4_NONE || current_state->board[i + 1][j] != C4_NONE) {
					score = 100;
					rule[6] += score;
				}//한쪽받침ㅇ
			}

			//2. \ (descending diagonal)
			if (i < 5 && i>1 && j < 4 && j>1 && current_state->board[i][j] == 1 && current_state->board[i - 2][j + 2] == 1 && current_state->board[i + 2][j - 2] == 1 && current_state->board[i - 1][j + 1] == C4_NONE && current_state->board[i + 1][j - 1] == C4_NONE) {
				if (current_state->board[i - 1][j] != C4_NONE && current_state->board[i + 1][j - 2] != C4_NONE) {
					score = 200;
					rule[6] += score;
				}//양쪽받침 ㅇ
				else if (current_state->board[i - 1][j] == C4_NONE && current_state->board[i + 1][j - 2] == C4_NONE) {
					score = 150;
					rule[6] += score;
				}
				else if (current_state->board[i - 1][j] != C4_NONE || current_state->board[i + 1][j - 2] != C4_NONE) {
					score = 100;
					rule[6] += score;
				}
			}
			//3. _0_0_ 가로   한칸띄워서 한쪽으로 본인의 돌이 한개
			if (i > 0 && i < 4 && current_state->board[i][j] == 1 && current_state->board[i + 2][j] == 1 && current_state->board[i - 1][j] == C4_NONE && current_state->board[i + 1][j] == C4_NONE && current_state->board[i + 3][j] == C4_NONE) {
				if (j > 0 && current_state->board[i + 1][j - 1] != C4_NONE) {
					score = 150;
					rule[6] += score;
				} //가운데 받침 0
				else if (j == 0) {
					score = 150;
					rule[6] += score;
				}
				else {
					score = 200;
					rule[6] += score;
				}
			}
			//3. /
			if (i < 5 && j>1 && j < 4 && i>1 && current_state->board[i][j] == C4_NONE && current_state->board[i - 2][j - 2] == C4_NONE && current_state->board[i + 2][j + 2] == C4_NONE && current_state->board[i - 1][j - 1] == 1 && current_state->board[i + 1][j + 1] == 1) {
				if (current_state->board[i][j - 1] != C4_NONE) {
					score = 150;
					rule[6] += score;
				}//가운데 받침 0
				else {
					score = 200;
					rule[6] += score;
				}
			}
			//3. \ (descending diagonal)
			if (i < 5 && j>1 && j < 4 && i>1 && current_state->board[i][j] == C4_NONE && current_state->board[i - 2][j + 2] == C4_NONE && current_state->board[i + 2][j - 2] == C4_NONE && current_state->board[i - 1][j + 1] == 1 && current_state->board[i + 1][j - 1] == 1) {
				if (current_state->board[i][j - 1] != C4_NONE) {
					score = 150;
					rule[6] += score;
				} //가운데 받침 ㅇ
				else {
					score = 200;
					rule[6] += score;
				}
			}
			//4. 한칸띄워서 내 돌 2개  00_0 가로
			if (i>2 && current_state->board[i][j] == 1 && current_state->board[i - 2][j] == 1 && current_state->board[i - 3][j] == 1 && current_state->board[i - 1][j] == C4_NONE) {
				if (j > 0 && current_state->board[i - 1][j - 1] != C4_NONE) {
					score = 300;
					rule[6] += score;
				}//받침있을 때
				else if (j == 0) {
					score = 300;
					rule[6] += score;
				}
				else {
					score = 1000;
					rule[6] += score;
				}
			}
			//4. /
			if (i < 4 && j < 3 && current_state->board[i][j] == 1 && current_state->board[i + 1][j + 1] == 1 && current_state->board[i + 2][j + 2] == C4_NONE && current_state->board[i + 3][j + 3] == 1) {
				if (current_state->board[i + 2][j + 1] != C4_NONE) {
					score = 300;
					rule[6] += score;
				}//받침 ㅇ
				else {
					score = 1000;
					rule[6] += score;
				}
			}
			//4. descending diagonal
			if (i < 4 && j > 2 && current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 2][j - 2] == C4_NONE && current_state->board[i + 3][j - 3] == 1) {
				if (current_state->board[i + 2][j - 3] != C4_NONE) {
					score = 300;
					rule[6] += score;
				}
				else {
					score = 1000;
					rule[6] += score;
				}
			}
			//5. 0_00 hori
			if (i > 3 && current_state->board[i][j] == 1 && current_state->board[i - 2][j] == C4_NONE && current_state->board[i - 3][j] == 1 && current_state->board[i - 1][j] == 1) {
				if (j > 0 && current_state->board[i - 2][j - 1] != C4_NONE) {
					score = 300;
					rule[6] += score;
				}//받침있을 때
				else if (j == 0) {
					score = 300;
					rule[6] += score;
				}
				else {
					score = 1000;
					rule[6] += score;
				}
			}
			//5. /
			if (i < 4 && j < 3 && current_state->board[i][j] == 1 && current_state->board[i + 1][j + 1] == C4_NONE && current_state->board[i + 2][j + 2] == 1 && current_state->board[i + 3][j + 3] == 1) {
				if (current_state->board[i + 1][j] != C4_NONE) {
					score = 300;
					rule[6] += score;
				}//받침 ㅇ
				else {
					score = 1000;
					rule[6] += score;
				}
			}
			//5. descending diagonal
			if (i < 4 && j > 2 && current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == C4_NONE && current_state->board[i + 2][j - 2] == 1 && current_state->board[i + 3][j - 3] == 1) {
				if (current_state->board[i + 1][j - 2] != C4_NONE) {
					score = 300;
					rule[6] += score;
				}
				else {
					score = 1000;
					rule[6] += score;
				}
			}

			//rule 8//
			/* rule 여기 두면 내가 2 */
			//00_0 이렇게 한칸 띄어서 본인돌이 있을 때
			//horizontal

			//first line
			/*
			if (i < 4 && j == 0 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 1 && current_state->board[i + 3][j] == 1 && current_state->board[i + 2][j] == C4_NONE) {
			score = 300;
			rule[7] += score;
			}*/

			if (i < 4 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 1 && current_state->board[i + 3][j] == 1 && current_state->board[i + 2][j] == C4_NONE) {
				//빈칸 밑에 받침이 없다.
				if (j>0 && current_state->board[i + 2][j - 1] == C4_NONE) {
					score = 1000;
					rule[7] += score;
					//printf("20_1\n");
				}
				//빈칸 밑에 받침이 있다. -> 바로 막혀서 점수 작게 줌.
				else if (j>0 && current_state->board[i + 2][j - 1] != C4_NONE) {
					score = 300;
					rule[7] += score;
				}
				else if (j == 0) {
					score = 300;
					rule[7] += score;
				}//first line
			}
			//diagonal descending 00_0
			if (i < 4 && j>2 && current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == 1 && current_state->board[i + 3][j - 3] == 1 && current_state->board[i + 2][j - 2] == C4_NONE) {
				//빈칸 밑에 받침이 없다.
				if (current_state->board[i + 2][j - 3] == C4_NONE) {
					score = 1000;
					rule[7] += score;
				}
				//빈칸 밑에 받침이 있다. -> 바로 막혀서 점수 작게 줌.
				else if (current_state->board[i + 2][j - 3] != C4_NONE) {
					score = 300;
					rule[7] += score;
				}
			}
			//diagonal ascending 00_0
			if (j < 3 && i < 4 && current_state->board[i][j] == 1 && current_state->board[i + 1][j + 1] == 1 && current_state->board[i + 3][j + 3] == 1 && current_state->board[i + 2][j + 2] == C4_NONE) {
				//빈칸 밑에 받침이 없다.
				if (current_state->board[i + 2][j + 1] == C4_NONE) {
					score = 1000;
					rule[7] += score;
				}
				//빈칸 밑에 받침이 있다. -> 바로 막혀서 점수 작게 줌.
				else if (current_state->board[i + 2][j + 1] != C4_NONE) {
					score = 300;
					rule[7] += score;
				}
			}

			//0_00 이렇게 한칸 띄어서 본인돌이 있을 때
			//horizontal
			//first line
			/*
			if (i < 4 && j == 0 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == C4_NONE && current_state->board[i + 3][j] == 1 && current_state->board[i + 2][j] == 1) {
			score = 300;
			rule[7] += score;
			}
			*/
			if (i < 4 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == C4_NONE && current_state->board[i + 3][j] == 1 && current_state->board[i + 2][j] == 1) {
				//빈칸 밑에 받침이 없다.
				if (j>0 && current_state->board[i + 1][j - 1] == C4_NONE) {
					score = 1000;
					rule[7] += score;
				}
				//빈칸 밑에 받침이 있다. -> 바로 막혀서 점수 작게 줌.
				else if (j>0 && current_state->board[i + 1][j - 1] != C4_NONE) {
					score = 300;
					rule[7] += score;
				}
				else if (j == 0) {
					score = 300;
					rule[7] += score;
				}
			}
			//diagonal descending 0_00
			if (i < 4 && j>2 && current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == C4_NONE && current_state->board[i + 3][j - 3] == 1 && current_state->board[i + 2][j - 2] == 1) {
				//빈칸 밑에 받침이 없다.
				if (current_state->board[i + 1][j - 2] == C4_NONE) {
					score = 1000;
					rule[7] += score;
				}
				//빈칸 밑에 받침이 있다. -> 바로 막혀서 점수 작게 줌.
				else if (current_state->board[i + 1][j - 2] != C4_NONE) {
					score = 300;
					rule[7] += score;
				}
			}
			//diagonal ascending 0_00
			if (i < 4 && j < 3 && current_state->board[i][j] == 1 && current_state->board[i + 1][j + 1] == C4_NONE && current_state->board[i + 3][j + 3] == 1 && current_state->board[i + 2][j + 2] == 1) {
				//빈칸 밑에 받침이 없다.
				if (current_state->board[i + 1][j] == C4_NONE) {
					score = 1000;
					rule[7] += score;
				}
				//빈칸 밑에 받침이 있다. -> 바로 막혀서 점수 작게 줌.
				else if (current_state->board[i + 1][j] != C4_NONE) {
					score = 300;
					rule[7] += score;
				}
			}
			//양쪽 비어 있어 4개 만들 가능성 있다. _oo_
			//horizontal
			if (i < 5 && i>0 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 1 && current_state->board[i - 1][j] == C4_NONE && current_state->board[i + 2][j] == C4_NONE) {
				if (j > 0 && current_state->board[i - 1][j - 1] == C4_NONE && current_state->board[i + 2][j - 1] == C4_NONE) {
					// 빈칸의 빈칸 두개 모두 empty
					score = 150;
					rule[7] += score;
				}
				else if (j > 0 && ((current_state->board[i - 1][j - 1] == C4_NONE && current_state->board[i + 2][j - 1] != C4_NONE) || (current_state->board[i - 1][j - 1] != C4_NONE && current_state->board[i + 2][j] == C4_NONE))) {
					// 빈칸의 빈칸 두개 중 하나가 empty
					score = 100;
					rule[7] += score;
				}
				else if (j > 0 && current_state->board[i - 1][j - 1] != C4_NONE && current_state->board[i + 2][j - 1] != C4_NONE) {
					// 빈칸의 빈칸 두개 모두 not empty
					score = 50;
					rule[7] += score;
				}
				else if (j == 0) {
					score = 50;
					rule[7] += score;
				}
			}
			//diagonal descending
			if (i<5 && i>0 && j<5 && j>1&&current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == 1 && current_state->board[i - 1][j + 1] == C4_NONE && current_state->board[i + 2][j - 2] == C4_NONE) {
				if (j>2 && current_state->board[i - 1][j] == C4_NONE && current_state->board[i + 2][j - 3] == C4_NONE) {
					// 빈칸의 빈칸 두개 모두 empty
					score = 150;
					rule[7] += score;
				}
				else if (j>2 && ((current_state->board[i - 1][j] == C4_NONE && current_state->board[i + 2][j - 3] != C4_NONE) || (current_state->board[i - 1][j] != C4_NONE && current_state->board[i + 2][j - 3] == C4_NONE))) {
					// 빈칸의 빈칸 두개 중 하나가 empty
					score = 100;
					rule[7] += score;
				}

				else if (j == 2 && current_state->board[i - 1][j] == C4_NONE) {//first line
					score = 100;
					rule[7] += score;

				}

				else if (j>2 && current_state->board[i - 1][j] != C4_NONE && current_state->board[i + 2][j - 3] != C4_NONE) {
					// 빈칸의 빈칸 두개 모두 not empty
					score = 50;
					rule[7] += score;
				}
				else if (j == 2 && current_state->board[i - 1][j] != C4_NONE) {
					score = 50;
					rule[7] += score;
				}

			}
			//diagonal ascending
			if (i > 0 && i < 5 && j < 4 && j>0&&current_state->board[i][j] == 1 && current_state->board[i + 1][j + 1] == 1 && current_state->board[i - 1][j - 1] == C4_NONE && current_state->board[i + 2][j + 2] == C4_NONE) {
				if (j > 1 && current_state->board[i - 1][j - 2] == C4_NONE && current_state->board[i + 2][j + 1] == C4_NONE) {
					// 빈칸의 빈칸 두개 모두 empty
					score = 150;
					rule[7] += score;
				}

				else if (j > 1 && ((current_state->board[i - 1][j - 2] == C4_NONE && current_state->board[i + 2][j + 1] != C4_NONE) || (current_state->board[i - 1][j - 2] != C4_NONE && current_state->board[i + 2][j + 1] == C4_NONE))) {
					// 빈칸의 빈칸 두개 중 하나가 empty
					score = 100;
					rule[7] += score;
				}

				else if (j == 1 && current_state->board[i + 2][j + 1] == C4_NONE) {
					score = 100;
					rule[7] += score;
				}

				else if (j > 1 && current_state->board[i - 1][j - 2] != C4_NONE && current_state->board[i + 2][j + 1] != C4_NONE) {
					// 빈칸의 빈칸 두개 모두 not empty
					score = 50;
					rule[7] += score;
				}

				else if (j == 1 && current_state->board[i + 2][j + 1] != C4_NONE) {
					score = 50;
					rule[7] += score;
				}
			}

			
			//한쪽이 막혀 있다. !OO? ?는 not empty !는 상대방돌이 아님
			//horizontal
			if (i<5 && i>0 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 1 && (current_state->board[i - 1][j] == 0 || current_state->board[i + 2][j] == 0)) {
				if ((current_state->board[i - 1][j] == 0 && current_state->board[i + 2][j] == 0)) {
					score = 5;
					rule[7] += score;
				}
				else {
					score = 10;
					rule[7] += score;
				}
				//printf("20\n");
			}

			if (i == 0 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 1) { // left wall
				if (current_state->board[i + 2][j] == 0) {
					score = 5;
					rule[7] += score;
				}
				else {
					score = 10;
					rule[7] += score;
				}
			}

			if (i == 5 && current_state->board[i][j] == 1 && current_state->board[i + 1][j] == 1) { // right wall
				if (current_state->board[i - 1][j] == 0) {
					score = 5;
					rule[7] += score;
				}
				else {
					score = 10;
					rule[7] += score;
				}
			}

			//diagonal descending _OO? (? : blocked)
			if (i>0 && j>1 && i<5 && j<5 && current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == 1 && (current_state->board[i - 1][j + 1] == 0 || current_state->board[i + 2][j - 2] == 0)) {
				if ((current_state->board[i - 1][j + 1] == 0 && current_state->board[i + 2][j - 2] == 0)) {
					score = 5;
					rule[7] += score;
				}
				else {
					score = 10;
					rule[7] += score;
				}
			}

			if (i == 0 && current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == 1) { // left wall
				if (j > 1 && current_state->board[i + 2][j - 2] == 0) {
					score = 5;
					rule[7] += score;
				}
				else {
					score = 10;
					rule[7] += score;
				}
			}

			if (i == 5 && current_state->board[i][j] == 1 && current_state->board[i + 1][j - 1] == 1) { // right wall
				if (j < 5 && current_state->board[i - 1][j + 1] == 0) {
					score = 5;
					rule[7] += score;
				}
				else {
					score = 10;
					rule[7] += score;
				}
			}


			//diagonal ascending
			if (i>0 && j>0 && i<5 && j<4 && current_state->board[i][j] == 1 && current_state->board[i + 1][j + 1] == 1 && (current_state->board[i - 1][j - 1] == 0 || current_state->board[i + 2][j + 2] == 0)) {
				if ((current_state->board[i - 1][j - 1] == 0 && current_state->board[i + 2][j + 2] == 0)) {
					score = 5;
					rule[7] += score;
				}
				else {
					score = 10;
					rule[7] += score;
				}
			}

			if (i == 0 && j < 5 && current_state->board[i][j] == 1 && current_state->board[i + 1][j + 1] == 1) { // left wall
				if (j < 4 && current_state->board[i + 2][j + 2] == 0) {
					score = 5;
					rule[7] += score;
				}
				else {
					score = 10;
					rule[7] += score;
				}
			}

			if (i == 5 && j < 5 && current_state->board[i][j] == 1 && current_state->board[i + 1][j + 1] == 1) { // right wall
				if (j > 0 && current_state->board[i - 1][j - 1] == 0) {
					score = 5;
					rule[7] += score;
				}
				else {
					score = 10;
					rule[7] += score;
				}
			}


			//column에만 두개 // vertical
			if (j>0 && j < 5 && current_state->board[i][j] == 1 && current_state->board[i][j - 1] == 1 && current_state->board[i][j + 1] == C4_NONE) {
				score = 10;
				rule[7] += score;
			}
		}
	}

	for (int l = 0; l < 8; l++) {
		total += rule[l];
		nthCol[l] = 0;
		if (rule[l] != 0) {
			nthCol[l] = l + 1;
		}
	}


	return total;
}

/****************************************************************************/
/**                                                                        **/
/**  This function returns a two-dimensional array containing the state of **/
/**  the game board.  Do not modify this array.  It is assumed that a game **/
/**  is in progress.  The value of this array is dynamic and will change   **/
/**  to reflect the state of the game as the game progresses.  It becomes  **/
/**  and stays undefined when the game ends.                               **/
/**                                                                        **/
/**  The first dimension specifies the column number and the second        **/
/**  dimension specifies the row number, where column and row numbering    **/
/**  start at 0 and the bottow row is considered the 0th row.  A value of  **/
/**  0 specifies that the position is occupied by a piece owned by player  **/
/**  0, a value of 1 specifies that the position is occupied by a piece    **/
/**  owned by player 1, and a value of C4_NONE specifies that the position **/
/**  is unoccupied.                                                        **/
/**                                                                        **/
/****************************************************************************/

char **
c4_board(void)
{
	assert(game_in_progress);
	return current_state->board;
}


/****************************************************************************/
/**                                                                        **/
/**  This function returns the "score" of the specified player.  This      **/
/**  score is a function of how many winning positions are still available **/
/**  to the player and how close he/she is to achieving each of these      **/
/**  positions.  The scores of both players can be compared to observe how **/
/**  well they are doing relative to each other.                           **/
/**                                                                        **/
/****************************************************************************/

int
c4_score_of_player(int player)
{
	assert(game_in_progress);
	return current_state->score[real_player(player)];
}


/****************************************************************************/
/**                                                                        **/
/**  This function returns true if the specified player has won the game,  **/
/**  and false otherwise.                                                  **/
/**                                                                        **/
/****************************************************************************/

bool
c4_is_winner(int player)
{
	assert(game_in_progress);
	return (current_state->winner == real_player(player));
}


/****************************************************************************/
/**                                                                        **/
/**  This function returns true if the board is completely full without a  **/
/**  winner, and false otherwise.                                          **/
/**                                                                        **/
/****************************************************************************/

bool
c4_is_tie(void)
{
	assert(game_in_progress);
	return (current_state->num_of_pieces == total_size &&
		current_state->winner == C4_NONE);
}


/****************************************************************************/
/**                                                                        **/
/**  This function returns the coordinates of the winning connections of   **/
/**  the winning player.  It is assumed that a player has indeed won the   **/
/**  game.  The coordinates are returned in x1, y1, x2, y2, where (x1, y1) **/
/**  specifies the lower-left piece of the winning connection, and         **/
/**  (x2, y2) specifies the upper-right piece of the winning connection.   **/
/**  If more than one winning connection exists, only one will be          **/
/**  returned.                                                             **/
/**                                                                        **/
/****************************************************************************/

void
c4_win_coords(int *x1, int *y1, int *x2, int *y2)
{
	register int i, j, k;
	int winner, win_pos = 0;
	bool found;

	assert(game_in_progress);

	winner = current_state->winner;
	assert(winner != C4_NONE);

	while (current_state->score_array[winner][win_pos] != magic_win_number)
		win_pos++;

	/* Find the lower-left piece of the winning connection. */

	found = false;
	for (j = 0; j<size_y && !found; j++)
		for (i = 0; i<size_x && !found; i++)
			for (k = 0; map[i][j][k] != -1; k++)
				if (map[i][j][k] == win_pos) {
					*x1 = i;
					*y1 = j;
					found = true;
					break;
				}

	/* Find the upper-right piece of the winning connection. */

	found = false;
	for (j = size_y - 1; j >= 0 && !found; j--)
		for (i = size_x - 1; i >= 0 && !found; i--)
			for (k = 0; map[i][j][k] != -1; k++)
				if (map[i][j][k] == win_pos) {
					*x2 = i;
					*y2 = j;
					found = true;
					break;
				}
}


/****************************************************************************/
/**                                                                        **/
/**  This function ends the current game.  It is assumed that a game is    **/
/**  in progress.  It is illegal to call any other game function           **/
/**  immediately after this one except for c4_new_game(), c4_poll() and    **/
/**  c4_reset().                                                           **/
/**                                                                        **/
/****************************************************************************/

void
c4_end_game(void)
{
	int i, j;

	assert(game_in_progress);
	assert(!move_in_progress);

	/* Free up the memory used by the map. */

	for (i = 0; i<size_x; i++) {
		for (j = 0; j<size_y; j++)
			free(map[i][j]);
		free(map[i]);
	}
	free(map);

	/* Free up the memory of all the states used. */

	for (i = 0; i<states_allocated; i++) {
		for (j = 0; j<size_x; j++)
			free(state_stack[i].board[j]);
		free(state_stack[i].board);
		free(state_stack[i].score_array[0]);
		free(state_stack[i].score_array[1]);
	}
	states_allocated = 0;

	/* Free up the memory used by the drop_order array. */

	free(drop_order);

	game_in_progress = false;
}


/****************************************************************************/
/**                                                                        **/
/**  This function resets the state of the algorithm to the starting state **/
/**  (i.e., no game in progress and a NULL poll function).  There should   **/
/**  no reason to call this function unless for some reason the calling    **/
/**  algorithm loses track of the game state.  It is illegal to call any   **/
/**  other game function immediately after this one except for             **/
/**  c4_new_game(), c4_poll() and c4_reset().                              **/
/**                                                                        **/
/****************************************************************************/

void
c4_reset(void)
{
	assert(!move_in_progress);
	if (game_in_progress)
		c4_end_game();
	poll_function = NULL;
}

/****************************************************************************/
/**                                                                        **/
/**  This function returns the RCS string representing the version of      **/
/**  this Connect-4 implementation.                                        **/
/**                                                                        **/
/****************************************************************************/

const char *
c4_get_version(void)
{
	return "$Id: c4.c,v 3.11 2009/11/03 14:42:01 pomakis Exp pomakis $";
}


/****************************************************************************/
/****************************************************************************/
/**                                                                        **/
/**  The following functions are local to this file and should not be      **/
/**  called externally.                                                    **/
/**                                                                        **/
/****************************************************************************/
/****************************************************************************/


/****************************************************************************/
/**                                                                        **/
/**  This function returns the number of possible win positions on a board **/
/**  of dimensions x by y with n being the number of pieces required in a  **/
/**  row in order to win.                                                  **/
/**                                                                        **/
/****************************************************************************/

static int
num_of_win_places(int x, int y, int n)
{
	if (x < n && y < n)
		return 0;
	else if (x < n)
		return x * ((y - n) + 1);
	else if (y < n)
		return y * ((x - n) + 1);
	else
		return 4 * x*y - 3 * x*n - 3 * y*n + 3 * x + 3 * y - 4 * n + 2 * n*n + 2;
}


/****************************************************************************/
/**                                                                        **/
/**  This function updates the score of the specified player in the        **/
/**  context of the current state,  given that the player has just placed  **/
/**  a game piece in column x, row y.                                      **/
/**                                                                        **/
/****************************************************************************/

static void
update_score(int player, int x, int y)
{
	register int i;
	int win_index;
	int this_difference = 0, other_difference = 0;
	int **current_score_array = current_state->score_array;
	int other_player = other(player);

	for (i = 0; map[x][y][i] != -1; i++) {
		win_index = map[x][y][i];
		this_difference += current_score_array[player][win_index];
		other_difference += current_score_array[other_player][win_index];

		current_score_array[player][win_index] <<= 1;
		current_score_array[other_player][win_index] = 0;

		if (current_score_array[player][win_index] == magic_win_number)
			if (current_state->winner == C4_NONE)
				current_state->winner = player;
	}

	current_state->score[player] += this_difference;
	current_state->score[other_player] -= other_difference;
}


/****************************************************************************/
/**                                                                        **/
/**  This function drops a piece of the specified player into the          **/
/**  specified column.  The row where the piece ended up is returned, or   **/
/**  -1 if the drop was unsuccessful (i.e., the specified column is full). **/
/**                                                                        **/
/****************************************************************************/

static int
drop_piece(int player, int column)
{
	int y = 0;

	while (current_state->board[column][y] != C4_NONE && ++y < size_y)
		;

	if (y == size_y)
		return -1;

	current_state->board[column][y] = player;
	current_state->num_of_pieces++;
	update_score(player, column, y);

	return y;
}


/****************************************************************************/
/**                                                                        **/
/**  This function pushes the current state onto a stack.  pop_state()     **/
/**  is used to pop from this stack.                                       **/
/**                                                                        **/
/**  Technically what it does, since the current state is considered to    **/
/**  be the top of the stack, is push a copy of the current state onto     **/
/**  the stack right above it.  The stack pointer (depth) is then          **/
/**  incremented so that the new copy is considered to be the current      **/
/**  state.  That way, all pop_state() has to do is decrement the stack    **/
/**  pointer.                                                              **/
/**                                                                        **/
/**  For efficiency, memory for each stack state used is only allocated    **/
/**  once per game, and reused for the remainder of the game.              **/
/**                                                                        **/
/****************************************************************************/

static void
push_state(void)
{
	register int i, win_places_array_size;
	Game_state *old_state, *new_state;

	win_places_array_size = win_places * sizeof(int);
	old_state = &state_stack[depth++];
	new_state = &state_stack[depth];

	if (depth == states_allocated) {

		/* Allocate space for the board */

		new_state->board = (char **)emalloc(size_x * sizeof(char *));
		for (i = 0; i<size_x; i++)
			new_state->board[i] = (char *)emalloc(size_y);

		/* Allocate space for the score array */

		new_state->score_array[0] = (int *)emalloc(win_places_array_size);
		new_state->score_array[1] = (int *)emalloc(win_places_array_size);

		states_allocated++;
	}

	/* Copy the board */

	for (i = 0; i<size_x; i++)
		memcpy(new_state->board[i], old_state->board[i], size_y);

	/* Copy the score array */

	memcpy(new_state->score_array[0], old_state->score_array[0],
		win_places_array_size);
	memcpy(new_state->score_array[1], old_state->score_array[1],
		win_places_array_size);

	new_state->score[0] = old_state->score[0];
	new_state->score[1] = old_state->score[1];
	new_state->winner = old_state->winner;
	new_state->num_of_pieces = old_state->num_of_pieces;

	current_state = new_state;
}


/****************************************************************************/
/**                                                                        **/
/**  This recursive function determines how good the current state may     **/
/**  turn out to be for the specified player.  It does this by looking     **/
/**  ahead level moves.  It is assumed that both the specified player and  **/
/**  the opponent may make the best move possible.  alpha and beta are     **/
/**  used for alpha-beta cutoff so that the game tree can be pruned to     **/
/**  avoid searching unneccessary paths.                                   **/
/**                                                                        **/
/**  The specified poll function (if any) is called at the appropriate     **/
/**  intervals.                                                            **/
/**                                                                        **/
/**  The worst goodness that the current state can produce in the number   **/
/**  of moves (levels) searched is returned.  This is the best the         **/
/**  specified player can hope to achieve with this state (since it is     **/
/**  assumed that the opponent will make the best moves possible).         **/
/**                                                                        **/
/****************************************************************************/

static int
evaluate(int player, int level, int alpha, int beta)
{
	if (poll_function != NULL && next_poll <= clock()) {
		next_poll += poll_interval;
		(*poll_function)();
	}

	if (current_state->winner == player)
		return INT_MAX - depth;
	else if (current_state->winner == other(player))
		return -(INT_MAX - depth);
	else if (current_state->num_of_pieces == total_size)
		return 0; /* a tie */
	else if (level == depth)
		return goodness_of(player);
	else {
		/* Assume it is the other player's turn. */
		int best = -(INT_MAX);
		int maxab = alpha;
		for (int i = 0; i<size_x; i++) {
			if (current_state->board[drop_order[i]][size_y - 1] != C4_NONE)
				continue; /* The column is full. */
			push_state();
			drop_piece(other(player), drop_order[i]);
			int goodness = evaluate(other(player), level, -beta, -maxab);
			if (goodness > best) {
				best = goodness;
				if (best > maxab)
					maxab = best;
			}
			pop_state();
			if (best > beta)
				break;
		}

		/* What's good for the other player is bad for this one. */
		return -best;
	}
}


/****************************************************************************/
/**                                                                        **/
/**  A safer version of malloc().                                          **/
/**                                                                        **/
/****************************************************************************/

static void *
emalloc(size_t size)
{
	void *ptr = malloc(size);
	if (ptr == NULL) {
		fprintf(stderr, "c4: emalloc() - Can't allocate %ld bytes.\n",
			(long)size);
		exit(1);
	}
	return ptr;
}