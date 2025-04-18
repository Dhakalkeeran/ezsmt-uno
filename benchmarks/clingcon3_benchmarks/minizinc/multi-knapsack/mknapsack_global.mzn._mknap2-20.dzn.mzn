%------------------------------------------------------------------------------%
% Multi Dimensional Knapsack Problem
%------------------------------------------------------------------------------%

include "knapsack.mzn";

%------------------------------------------------------------------------------%
% Parameters

int: N; % number of variables
int: M; % number of constraints

set of int: VRange = 1..N;
set of int: CRange = 1..M;

array[CRange,VRange] of int: a;     % Weight of items per bin
array[CRange] of int: b;            % Sizes of bins
array[VRange] of int: c;            % Profit of items

%------------------------------------------------------------------------------%
% Ignored parameters

int: z;                             % Normally the optimal value

%------------------------------------------------------------------------------%
% Variables

array[VRange] of var 0..1: x;               % Whether an item is packed
array[CRange] of var 0..ub_array(b): bVar;  % Total weight in a bin

var 0..sum(c): objective = sum(i in VRange)(c[i] * x[i]);   % Total profit

%------------------------------------------------------------------------------%
% Constraints

    % Constraining the size of the bins
    %
constraint
	forall(i in CRange)( bVar[i] >= 0 /\ bVar[i] <= b[i] );

    % Knapsack constraints
    %
constraint
	forall(i in CRange)( 
        knapsack([a[i,j] | j in VRange], c, x, bVar[i], z) 
    );  

%------------------------------------------------------------------------------%
% Some integrety check for the (input) data

constraint 
    forall(i in CRange,j in VRange)(
        assert(a[i,j] >= 0, "negative values in a") 
    );
constraint 
    forall(i in CRange)( assert(b[i] >= 0, "negative values in b") );
constraint 
    forall(j in VRange)( assert(c[j] >= 0, "negative values in c") );
constraint assert(z >= 0, "negative z");

%------------------------------------------------------------------------------%
% Search

solve 
    :: int_search(x, input_order, indomain_max, complete)
    maximize objective;

%------------------------------------------------------------------------------%
% Output

output [ 
    "x = ", show(x), ";\n",
    "objective = ", show(objective), ";\n"
];

%------------------------------------------------------------------------------%
N=50;
M=5;

z=6339;
c=[360, 83, 59, 130, 431, 67, 230, 52, 93, 125, 670, 892, 600, 38, 48, 147, 78, 256, 63, 17, 120, 164, 432, 35, 92, 110, 22, 42, 50, 323, 514, 28, 87, 73, 78, 15, 26, 78, 210, 36, 85, 189, 274, 43, 33, 10, 19, 389, 276, 312];

b=[850, 1400, 1500, 450, 1100];
a=[|
7, 0, 30, 22, 80, 94, 11, 81, 70, 64, 59, 18, 0, 36, 3, 8, 15, 42, 9, 0, 42, 47, 52, 32, 26, 48, 55, 6, 29, 84, 2, 4, 18, 56, 7, 29, 93, 44, 71, 3, 86, 66, 31, 65, 0, 79, 20, 65, 52, 13|
8, 66, 98, 50, 0, 30, 0, 88, 15, 37, 26, 72, 61, 57, 17, 27, 83, 3, 9, 66, 97, 42, 2, 44, 71, 11, 25, 74, 90, 20, 0, 38, 33, 14, 9, 23, 12, 58, 6, 14, 78, 0, 12, 99, 84, 31, 16, 7, 33, 20|
3, 74, 88, 50, 55, 19, 0, 6, 30, 62, 17, 81, 25, 46, 67, 28, 36, 8, 1, 52, 19, 37, 27, 62, 39, 84, 16, 14, 21, 5, 60, 82, 72, 89, 16, 5, 29, 7, 80, 97, 41, 46, 15, 92, 51, 76, 57, 90, 10, 37|
21, 40, 0, 6, 82, 91, 43, 30, 62, 91, 10, 41, 12, 4, 80, 77, 98, 50, 78, 35, 7, 1, 96, 67, 85, 4, 23, 38, 2, 57, 4, 53, 0, 33, 2, 25, 14, 97, 87, 42, 15, 65, 19, 83, 67, 70, 80, 39, 9, 5|
94, 86, 80, 92, 31, 17, 65, 51, 46, 66, 44, 3, 26, 0, 39, 20, 11, 6, 55, 70, 11, 75, 82, 35, 47, 99, 5, 14, 23, 38, 94, 66, 64, 27, 77, 50, 28, 25, 61, 10, 30, 15, 12, 24, 90, 25, 39, 47, 98, 83|];
