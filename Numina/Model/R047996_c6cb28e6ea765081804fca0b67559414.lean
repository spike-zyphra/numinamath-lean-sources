import Mathlib

theorem algebra_20849 : IsGreatest {x : ℝ | ∃(a b c d : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ a + b + c + d = 1 ∧ x = a * b + b * c + c * d} (1/4 : ℝ) := by
  constructor
  · -- First part: show 1/4 is in the set
    use 0, (1 / 2), (1 / 2), 0
    norm_num
  · -- Second part: show that for any particular element x in the set, 1/4 ≥ x
    intro x hx
    rcases hx with ⟨a, b, c, d, ha, hb, hc, hd, h1, hx⟩
    nlinarith [sq_nonneg (b - c), sq_nonneg (a + c - (b + d)), sq_nonneg (a + d - (b + c)), 
              sq_nonneg (b + c - 1 / 2), sq_nonneg (a + d - 1 / 2), 
              mul_nonneg ha hb, mul_nonneg hb hc, 
              mul_nonneg hc hd, 
              mul_nonneg (show 0 ≤ a + c by linarith) (show 0 ≤ b + d by linarith)]