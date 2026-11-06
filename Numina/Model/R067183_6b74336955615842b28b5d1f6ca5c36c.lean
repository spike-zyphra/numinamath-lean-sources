import Mathlib

theorem algebra_12725 : IsGreatest {z|∃ a b c : ℝ, a+b+c=a^2+b^2+c^2 ∧ z=a+b+c} 3 := by
  constructor
  · -- First part: Show that 3 is in the set
    use 1, 1, 1
    norm_num
  · -- Second part: Show that 3 is greatest, i.e., any element in the set is ≤ 3
    intro z hz
    rcases hz with ⟨a, b, c, h, h1⟩
    have h2 : a + b + c = a^2 + b^2 + c^2 := by linarith
    have h3 : (a - 1)^2 + (b - 1)^2 + (c - 1)^2 ≥ 0 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    nlinarith [h2]