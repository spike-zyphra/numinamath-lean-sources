import Mathlib

/-!
A $5 \times 5$ square grid has the number -3 written in the upper-left square
and the number 3 written in the lower-right square.
In how many ways can the remaining squares be filled in with integers so that any two adjacent numbers differ by 1 ,
where two squares are adjacent if they share a common edge (but not if they share only a corner)?
-/

-- Let N be the dimension of the grid.
abbrev N : Nat := 5

-- The problem uses 1-based indexing for rows and columns (i, j from 1 to N).
-- Let's define the index function as given.
-- k_val is the number in the square (i,j)
abbrev calculate_index (i j k_val : Int) : Int :=
  i + j - k_val

-- For the upper-left square (1,1) with value -3:
abbrev ul_row : Int := 1
abbrev ul_col : Int := 1
abbrev ul_val : Int := -3
abbrev ul_index : Int := calculate_index ul_row ul_col ul_val

-- For the lower-right square (N,N) with value 3:
abbrev lr_row : Int := N
abbrev lr_col : Int := N
abbrev lr_val : Int := 3
abbrev lr_index : Int := calculate_index lr_row lr_col lr_val

-- Verify the indices calculated in the problem description.
lemma ul_index_val : ul_index = 5 := by
  simp [ul_index, calculate_index, ul_row, ul_col, ul_val]

lemma lr_index_val : lr_index = 7 := by
  simp [lr_index, calculate_index, lr_row, lr_col, lr_val, N]

/-
The argument states that any square (r,c) must have index $x_{rc} = 5$ or $x_{rc} = 7$.
This is because:
1. $x_{11} = 5$.
2. If square $S_1$ at $(r,c)$ has index $x_1$, and $S_2$ at $(r,c+1)$ has index $x_2$.
   $x_1 = r+c-k_1$
   $x_2 = r+(c+1)-k_2$
   $x_2 - x_1 = (r+c+1-k_2) - (r+c-k_1) = 1 - (k_2 - k_1)$.
   Since $|k_1-k_2|=1$, $k_2-k_1 = \pm 1$.
   If $k_2-k_1 = 1$, then $x_2-x_1 = 1-1 = 0 \implies x_2=x_1$.
   If $k_2-k_1 = -1$, then $x_2-x_1 = 1-(-1) = 2 \implies x_2=x_1+2$.
   The same applies for vertical adjacency.
3. Any path from (1,1) to (N,N) using only rightward and downward steps involves indices
   that are non-decreasing and can only increase by 0 or 2 at each step.
4. Since $x_{11}=5$ and $x_{NN}=7$, any intermediate index must be 5 or 7. If an index were,
   for example, 3, it could not reach 5. If it were 6, it could not be formed from 5 by adding
   multiples of 2. If it were 9, it could reach 7 from it by subsequent steps.
   Specifically, any path from $(1,1)$ to $(i,j)$ results in $x_{ij} \ge x_{11}$.
   Any path from $(i,j)$ to $(N,N)$ means $x_{NN} \ge x_{ij}$ (if steps are always +0 or +2).
   So $5 \le x_{ij} \le 7$. Since $x_{ij}$ must have the same parity as $x_{11}$ if all steps are +0/+2,
   and $x_{11}=5$ is odd, $x_{ij}$ must be odd. Thus $x_{ij}$ can only be 5 or 7.
-/

-- The number of ways is identified as the number of paths from the
-- lower-left corner (of the grid lines, e.g., point (0,N) or (1,N+1) depending on convention)
-- to the upper-right corner (e.g., point (N,0) or (N+1,1)).
-- Such a path consists of N upward steps and N rightward steps.
-- The total number of steps is N + N = 2N.
-- The number of ways to choose N positions for the upward steps (or rightward steps)
-- out of 2N total steps is $\binom{2N}{N}$.

abbrev num_steps_up : Nat := N
abbrev num_steps_right : Nat := N
abbrev total_steps : Nat := num_steps_up + num_steps_right

lemma total_steps_val : total_steps = 2 * N := by
  simp [total_steps, num_steps_up, num_steps_right]
  rw [Nat.two_mul]

abbrev total_paths : Nat := Nat.choose total_steps num_steps_up

-- For N=5, total_steps = 10, num_steps_up = 5.
-- total_paths = $\binom{10}{5}$.
lemma total_paths_N5 : total_paths = Nat.choose (2*N) N := by
  simp [total_paths, total_steps_val, num_steps_right, num_steps_up]

-- Calculate $\binom{10}{5}$:
-- $\binom{10}{5} = \frac{10 \times 9 \times 8 \times 7 \times 6}{5 \times 4 \times 3 \times 2 \times 1} = 2 \times 9 \times 2 \times 7 \times 1 = 252$.
lemma binom_10_5_eval : Nat.choose 10 5 = 252 := by
  rfl -- Lean's `Nat.choose` can compute this directly.

-- The problem states that two of these paths are invalid:
-- 1. The path that effectively makes all squares have index 5. (UL index is 5, LR index becomes 5, but needs to be 7).
-- 2. The path that effectively makes all squares have index 7. (UL index becomes 7, but needs to be 5. LR index is 7).
abbrev num_invalid_paths : Nat := 2

-- The number of valid ways to fill the grid is the total number of paths minus the invalid ones.
abbrev numberOfWays : Nat := total_paths - num_invalid_paths

-- Final calculation
theorem final_answer : numberOfWays = 250 := by
  rw [numberOfWays]
  rw [total_paths_N5]
  have h_N : N = 5 := rfl
  rw [h_N]
  rw [binom_10_5_eval]
  rw [num_invalid_paths]
