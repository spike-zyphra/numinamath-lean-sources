import Mathlib

theorem algebra_7087 : IsGreatest {x : ℤ | ∃ a b c d : ℤ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a + b + c + d = 63 ∧ x = a * b + b * c + c * d} 991 := by
  constructor
  · -- Show 991 is in the set by choosing a = 1, b = 30, c = 31, d = 1
    use 1, 30, 31, 1
    all_goals norm_num
  · -- Show that any value in the set is ≤ 991
    intro x hx
    rcases hx with ⟨a, b, c, d, ha, hb, hc, hd, h, hx⟩
    nlinarith [sq_nonneg (a + c - 31 : ℤ), sq_nonneg (b + d - 31 : ℤ), sq_nonneg ((a + c) - (b + d) : ℤ), sq_nonneg (a - 1 : ℤ), sq_nonneg (b - 31 : ℤ), sq_nonneg (c - 1 : ℤ), sq_nonneg (d - 30 : ℤ),
      mul_pos ha hb, mul_pos hb hc, mul_pos hc (show 0 < d by linarith)]