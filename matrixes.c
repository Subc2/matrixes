/* matrixes - simplifies matrixes and solves systems of linear equations
 * Copyright (C) 2015-2016 Paweł Zacharek
 * 
 * -----------------------------------------------------------------------
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 * -----------------------------------------------------------------------
 * 
 * date: 2016-02-02
 * compiling: gcc -std=gnu11 -o matrixes.elf matrixes.c
 */

#include <errno.h>
#include <getopt.h>
#include <limits.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define INT_BIT (CHAR_BIT * sizeof(int))
#define MAX_PRIME USHRT_MAX

typedef struct {
	int numerator;
	int denominator;
} fraction;

int *prime_numbers = NULL;

void initialize_prime_numbers(void)
{
	const int sieve_size = ((MAX_PRIME + 1) * sizeof(int) + (INT_BIT - 1)) / INT_BIT;
	int number_of_primes = 0;
	int *sieve = malloc(sieve_size);
	memset(sieve, '\xff', sieve_size);  // sets primality bit for all numbers
	sieve[0] &= ~((1 << 0) | (1 << 1));  // 0 and 1 aren't primes
	for (int i = 2; i < MAX_PRIME + 1; ++i)
		if (sieve[i / INT_BIT] & (1 << i % INT_BIT)) {  // 'i' is a prime number
			for (int j = 2 * i; j < MAX_PRIME + 1; j += i)  // 'i' multiples aren't primes
				sieve[j / INT_BIT] &= ~(1 << (j % INT_BIT));  // removes primality bit
			++number_of_primes;
		}
	prime_numbers = (int *)malloc((number_of_primes + 1) * sizeof(int));
	for (int i = 0, j = 0; j < number_of_primes; ++i)
		if (sieve[i / INT_BIT] & (1 << (i % INT_BIT)))
			prime_numbers[j++] = i;
	prime_numbers[number_of_primes] = 0;
	free(sieve);
	return;
}

void clear_prime_numbers(void)
{
	free(prime_numbers);
	prime_numbers = NULL;
	return;
}

fraction reduction(fraction x)
{
	if (x.denominator < 0) {
		x.numerator *= -1;
		x.denominator *= -1;
	}
	if (x.numerator == 0)
		x.denominator = 1;
	else if (abs(x.numerator) == x.denominator) {  // simplifying by numbers greater than those from array 'prime_numbers'
		x.numerator /= x.denominator;
		x.denominator /= x.denominator;
	} else  // simplifying by remaining numbers
		for (int i = 0; prime_numbers[i] <= abs(x.numerator) && prime_numbers[i] <= x.denominator && prime_numbers[i] != 0; ++i)
			while (x.numerator % prime_numbers[i] == 0 && x.denominator % prime_numbers[i] == 0) {
				x.numerator /= prime_numbers[i];
				x.denominator /= prime_numbers[i];
			}
	return x;
}

static inline double double_div(double a, double b)
{
	return a / b;
}

static inline fraction fraction_div(fraction a, fraction b)
{
	a.numerator *= b.denominator;
	a.denominator *= b.numerator;
	return reduction(a);
}

static inline double double_mul(double a, double b)
{
	return a * b;
}

static inline fraction fraction_mul(fraction a, fraction b)
{
	a.numerator *= b.numerator;
	a.denominator *= b.denominator;
	return reduction(a);
}

static inline double double_int2type(int x)
{
	return (double)x;
}

static inline fraction fraction_int2type(int x)
{
	fraction value = {x, 1};
	return value;
}

static inline bool double_is_zero(double x)
{
	return x == 0 ? 1 : 0;
}

static inline bool fraction_is_zero(fraction x)
{
	return x.numerator == 0 ? 1 : 0;
}

static inline double double_sub(double a, double b)
{
	return a - b;
}

static inline fraction fraction_sub(fraction a, fraction b)
{
	a.numerator = a.numerator * b.denominator - b.numerator * a.denominator;
	a.denominator *= b.denominator;
	return reduction(a);
}

void read_matrix_double(int rows, int columns, double *matrix[])
{
	for (int y = 0; y < rows; ++y)
		for (int x = 0; x < columns; ++x)
			scanf("%lf", &matrix[y][x]);
	return;
}

void read_matrix_fraction(int rows, int columns, fraction *matrix[])
{
	char division_sign;
	for (int y = 0; y < rows; ++y)
		for (int x = 0; x < columns; ++x) {
			scanf("%d%c", &matrix[y][x].numerator, &division_sign);
			if (division_sign == '/')
				scanf("%d", &matrix[y][x].denominator);
			else
				matrix[y][x].denominator = 1;
		}
	return;
}

#define simplify_matrix(TYPE)\
void simplify_matrix_##TYPE(int rows, int columns, TYPE *matrix[])\
{\
	int x0, y0;  /* basic coordinates */\
	for (x0 = y0 = 0; x0 < columns && y0 < rows; ++x0, ++y0) {  /* Forward Elimination */\
		/* equation with leading coefficient must be the first */\
		if (TYPE##_is_zero(matrix[y0][x0]))\
			for (int y = y0 + 1; y < rows; ++y)\
				if (!TYPE##_is_zero(matrix[y][x0])) {\
					TYPE *tmp = matrix[y0];\
					matrix[y0] = matrix[y];\
					matrix[y] = tmp;\
					break;\
				}\
		if (TYPE##_is_zero(matrix[y0][x0]))  /* pivot is missing */\
			continue;\
		/* pivot has to be equal to 1 (giving us monic polynomial) */\
		TYPE multiplier = TYPE##_div(TYPE##_int2type(1), matrix[y0][y0]);\
		for (int x = x0; x < columns; ++x)\
			matrix[y0][x] = TYPE##_mul(matrix[y0][x], multiplier);\
	  /* we're getting rid of variables in the same column as pivot */\
		for (int y = y0 + 1; y < rows; ++y)\
			if (!TYPE##_is_zero(matrix[y][x0])) {\
				TYPE multiplier = matrix[y][x0];\
				matrix[y][x0] = TYPE##_int2type(0);  /* this result can be predicted */\
				for (int x = x0 + 1; x < columns; ++x)\
					matrix[y][x] = TYPE##_sub(matrix[y][x], TYPE##_mul(matrix[y0][x], multiplier));\
			}\
	}\
	for (--y0; y0 > 0; --y0) {  /* back substitution */\
		/* we're looking for pivot */\
		for (x0 = 0; x0 < columns - 1 && TYPE##_is_zero(matrix[y0][x0]); ++x0);\
		if (TYPE##_is_zero(matrix[y0][x0]))\
			continue;\
	  /* we're getting rid of variables in the same column as pivot */\
		for (int y = y0 - 1; y >= 0; --y)\
			if (!TYPE##_is_zero(matrix[y][x0])) {\
				TYPE multiplier = matrix[y][x0];\
				matrix[y][x0] = TYPE##_int2type(0);  /* this result can be predicted */\
				for (int x = x0 + 1; x < columns; ++x)\
					matrix[y][x] = TYPE##_sub(matrix[y][x], TYPE##_mul(matrix[y0][x], multiplier));\
			}\
	}\
	return;\
}
simplify_matrix(double)
simplify_matrix(fraction)

void write_matrix_double(int rows, int columns, double *matrix[])
{
	for (int y = 0; y < rows; ++y) {
		for (int x = 0; x < columns; ++x) {
			printf("%lf", matrix[y][x]);
			if (x < columns - 1)
				putchar('\t');
		}
		putchar('\n');
	}
	return;
}

void write_matrix_fraction(int rows, int columns, fraction *matrix[])
{
	for (int y = 0; y < rows; ++y) {
		for (int x = 0; x < columns; ++x) {
			if (matrix[y][x].denominator == 1)
				printf("%d", matrix[y][x].numerator);
			else
				printf("%d/%d", matrix[y][x].numerator, matrix[y][x].denominator);
			if (x < columns - 1)
				putchar('\t');
		}
		putchar('\n');
	}
	return;
}

int main(int argc, char *argv[])
{
	const char *Help = "matrixes - simplifies matrixes and solves systems of linear equations\n"
	"Syntax: matrixes [arguments]\n"
	"Arguments:\n"
	"  -e, --equation    solve a system of linear equations\n"
	"  -m, --matrix      simplify a matrix using Gaussian elimination\n"
	"  -h, --help        print this help text\n"
	"  -d, --double      use floating-point arithmetic\n"
	"  -f, --fraction    use rational number arithmetic\n"
	"  -q, --quiet       display pure answer";
	struct structure_parameters {
		bool equation;
		bool fraction;
		bool quiet;
	} parameters = {0, 0, 0};
	const struct option long_options[] = {
		{"double", 0, NULL, 'd'},
		{"equation", 0, NULL, 'e'},
		{"fraction", 0, NULL, 'f'},
		{"help", 0, NULL, 'h'},
		{"matrix", 0, NULL, 'm'},
		{"quiet", 0, NULL, 'q'},
		{NULL, 0, NULL, 0}
	};
	for (int option, long_option_index; (option = getopt_long(argc, argv, "defhmq", long_options, &long_option_index)) != -1;)
		switch (option) {
			case 'd':
				parameters.fraction = 0;
				break;
			case 'e':
				parameters.equation = 1;
				break;
			case 'f':
				parameters.fraction = 1;
				break;
			case 'h':
				puts(Help);
				return 0;
			case 'm':
				parameters.equation = 0;
				break;
			case 'q':
				parameters.quiet = 1;
				break;
			default:
				return EINVAL;
		}
	int rows, columns;
	if (parameters.quiet != 1)
		puts(parameters.equation == 1
			? "Enter the number of equations and the number of unknowns:"
			: "Enter height and width of the matrix:"
		);
	scanf("%d %d", &rows, &columns);
	if (parameters.equation == 1)
		++columns;
	void **matrix = (void **)malloc(rows * (parameters.fraction == 1 ? sizeof(fraction *) : sizeof(double *)));
	for (int i = 0; i < rows; ++i)
		matrix[i] = malloc(columns *  (parameters.fraction == 1 ? sizeof(fraction) : sizeof(double)));
	if (parameters.quiet != 1) {
		char division_sign = (parameters.fraction == 1 ? '/' : '.');
		if (parameters.equation == 1)
			printf("For every equation enter coefficients of the consecutive variables and\n"
			"the constant term, e.g. for \"(1%c2)*a + 1*b + 2*c = 4\" enter \"1%c2 1 2 4\":\n",
			division_sign, division_sign);
		else
			printf("Enter values of matrix fields%s\n", parameters.fraction == 1 ? ". For fractions use notation \"p/q\":" : ":");
	}
	if (parameters.fraction == 1) {
		initialize_prime_numbers();  // we won't notice delay while typing data manually
		read_matrix_fraction(rows, columns, (fraction **)matrix);
		simplify_matrix_fraction(rows, columns, (fraction **)matrix);
	} else {
		read_matrix_double(rows, columns, (double **)matrix);
		simplify_matrix_double(rows, columns, (double **)matrix);
	}
	if (parameters.quiet != 1)
		puts(parameters.equation == 1
			? "The matrix representing this linear system is as follows:"
			: "Simplified matrix:"
		);
	if (parameters.fraction == 1) {
		write_matrix_fraction(rows, columns, (fraction **)matrix);
		clear_prime_numbers();
	} else
		write_matrix_double(rows, columns, (double **)matrix);
	for (int i = 0; i < rows; ++i)
		free(matrix[i]);
	free(matrix);
	return 0;
}
