import Mathlib

open Finset


theorem algebra_109627 {A : ℝ} (hA : A = 53 * ∑ i ∈ range 2013, ((1:ℝ) / ((i + 1) * (i + 2)))) : A = 2013/38 ∧ (∃ a b c d e : ℕ, (A = (a * b * c : ℝ) / (d * e) ∧ (Nat.digits 10 a).sum + (Nat.digits 10 b).sum + (Nat.digits 10 c).sum = (Nat.digits 10 d).sum + (Nat.digits 10 e).sum)) := by
  have Aeq: A = 2013/38 := by
    rw [hA]
    norm_num [sum_range_succ]
  constructor
  exact Aeq
  use 3, 11, 61, 2, 19
  constructor
  rw [Aeq]
  norm_num
  all_goals norm_num