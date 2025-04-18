%-----------------------------------------------------------------------------%
% Radiation problem, MiniZinc 2.0.4 version
%
%-----------------------------------------------------------------------------%

%-----------------------------------------------------------------------------%
% Parameters
%-----------------------------------------------------------------------------%

int: m;  % Rows
int: n;  % Columns

set of int: Rows    = 1..m;
set of int: Columns = 1..n;

	% Intensity matrix
array[Rows, Columns] of int: Intensity;


set of int: BTimes = 1..Bt_max;

int: Bt_max   = max(i in Rows, j in Columns) (Intensity[i,j]);
int: Ints_sum = sum(i in Rows, j in Columns) (Intensity[i,j]);

%-----------------------------------------------------------------------------%
% Variables
%-----------------------------------------------------------------------------%

	% Total beam-on time
var 0..Ints_sum: Beamtime;

	% Number of shape matrices
var 0..m*n: K;

	% N[b] is the number of shape matrices with associated beam-on time b
array[BTimes] of var 0..m*n: N;

	% Q[i,j,b] is the number of shape matrices with associated beam-on time
	% b that expose cell (i,j)
array[Rows, Columns, BTimes] of var 0..m*n: Q;

%-----------------------------------------------------------------------------%
% Constraints
%-----------------------------------------------------------------------------%

	% For FD/LP hybrid solving, all these should go the LP solver
	% (with a suitable linearisation of the 'max' expressions).
constraint
	Beamtime = sum(b in BTimes) (b * N[b])
	/\
	K = sum(b in BTimes) (N[b])
	/\
	forall(i in Rows, j in Columns)
		( Intensity[i,j] = sum([b * Q[i,j,b] | b in BTimes]) )
	/\
	forall(i in Rows, b in BTimes)
		( upper_bound_on_increments(N[b], [Q[i,j,b] | j in Columns]) );


predicate upper_bound_on_increments(var int: N_b, array[int] of var int: L) =
	N_b >= L[1] + sum([ max(L[j] - L[j-1], 0) | j in 2..n ]);
	%
	% Good linear version:
	% let { array[min(index_set(L))..max(index_set(L))] of var int: S } in
	% N_b >= L[1] + sum([ S[j] | j in 2..n ]) /\
	% forall([ S[j] >= L[j] - L[j-1] /\ S[j] >= 0 | j in 2..n ]);
	

%-----------------------------------------------------------------------------%
% Objective
%-----------------------------------------------------------------------------%
int: obj_min = lb((m*n + 1) * Beamtime + K);
int: obj_max = ub((m*n + 1) * Beamtime + K);
var obj_min..obj_max: objective = (m*n + 1) * Beamtime + K;

solve 
    :: int_search(
		[Beamtime] ++ N ++
	    	[Q[i,j,b] | i in Rows, j in Columns, b in BTimes ],
		input_order, indomain_split, complete)
	minimize objective;
		% really: (Beamtime, K),  i.e. in lexicographic order

%-----------------------------------------------------------------------------%

output [
	"objective = \(objective);\n",
    "Beamtime = \(Beamtime);\n",
    "K = \(K);\n",
    "N = \(N);\n",
    "Q = array3d(\(Rows), \(Columns), \(BTimes), \(Q));\n"
];

%-----------------------------------------------------------------------------%
%-----------------------------------------------------------------------------%

m = 9;	% rows
n = 9;	% columns

% max intensity = 11
Intensity = [|
 4,  8, 11,  2,  5,  7,  1, 10,  4 |
11,  4,  4,  5,  1,  8,  9,  3,  9 |
 2,  9,  6,  2,  4,  1,  5,  2,  6 |
11,  9,  8,  9,  3,  2, 11,  6,  7 |
 2,  8, 11,  2, 10,  5,  5,  4,  5 |
 5,  9,  8,  1,  6,  3,  5, 11,  5 |
 6,  5,  9,  9,  2,  9,  8,  2,  2 |
 9,  7,  8,  3,  7,  6,  7,  4, 11 |
 7,  1,  6, 10,  0,  8,  1,  0,  0
|];

