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

m = 6;	% rows
n = 6;	% columns

% max intensity = 21
Intensity = [|
17, 19,  2, 15, 21,  5 |
 3, 15,  1,  1, 12, 18 |
 2, 13,  7,  0, 18,  4 |
 6,  8, 17, 21,  6,  2 |
 4, 12, 13, 10, 21,  5 |
13, 18, 20, 12,  6, 17
|];

