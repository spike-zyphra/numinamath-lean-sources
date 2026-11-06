import Mathlib
open Nat

/- At the end of a chess tournament that lasted for k rounds,
   it turned out that the number of points scored by the participants
   formed a geometric progression with a natural denominator greater than 1.
   How many participants could there have been:
   a) when k = 1989
   b) when k = 1988? -/

namespace number_theory_214071

/-- Sum of the geometric progression A, Ap, …, Ap^(n-1) as a natural number. -/
def gp_sum (A p n : ℕ) : ℕ := A * (p ^ n - 1) / (p - 1)

/-- Valid scoring: there exist A > 0 and p > 1 such that the GP sum is k
    and the top score A * p^(n-1) does not exceed k. -/
def valid_score (k n : ℕ) : Prop :=
  ∃ A p : ℕ, p > 1 ∧ A > 0 ∧ gp_sum A p n = k ∧ A * p ^ (n - 1) ≤ k

/-- Subproblem (a): k = 1989. Possible participant counts: n = 2 or n = 3. -/
theorem number_theory_214071_1 : valid_score 1989 2 ∧ valid_score 1989 3 := by
  -- Exhibit (A, p) for each case
  constructor
  · -- Case n = 2: choose A = 663, p = 2 so gp_sum 663 2 2 = 1989
    use 663, 2
    simp only [gp_sum]
    norm_num
  · -- Case n = 3: choose A = 153, p = 3 so gp_sum 153 3 3 = 1989
    use 153, 3
    simp only [gp_sum]
    norm_num

/-- Subproblem (b): k = 1988. Possible participant counts: n = 2 or n = 3. -/
theorem number_theory_214071_2 : valid_score 1988 2 ∧ valid_score 1988 3 := by
  -- Exhibit (A, p) for each case
  constructor
  · -- Case n = 2: choose A = 497, p = 3 so gp_sum 497 3 2 = 1988
    use 497, 3
    simp only [gp_sum]
    norm_num
  · -- Case n = 3: choose A = 284, p = 2 so gp_sum 284 2 3 = 1988
    use 284, 2
    simp only [gp_sum]
    norm_num

end number_theory_214071