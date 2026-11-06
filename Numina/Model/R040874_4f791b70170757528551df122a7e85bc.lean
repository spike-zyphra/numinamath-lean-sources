import Mathlib

theorem algebra_204592 :
  IsGreatest {s | ∃ (a b c d : ℕ), 
    a < b ∧ b < c ∧ c < d ∧
    (c + d) + (b + d) + (a + b + c) + (a + b + d) = 2017 ∧
    s = a + b + c + d} 806 := by
  constructor
  · -- Show that 806 is in the set
    use 199, 201, 202, 204
    all_goals norm_num
  · -- Show that any s in the set is at most 806
    intro s hs
    rcases hs with ⟨a, b, c, d, hab, hbc, hcd, hsum, heq⟩
    have eq_simplify : 2 * (a + b + c + d) + (b + d) = 2017 := by
      linarith
    have h1 : a + b + c + d ≤ 806 := by
      omega
    omega