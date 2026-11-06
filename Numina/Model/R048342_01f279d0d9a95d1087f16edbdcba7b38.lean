import Mathlib

theorem algebra_236830 (f : ℝ → ℝ) (hf : f = fun x => (5 - 4 * x + x ^ 2) / (2 - x)) :
    IsLeast {x | ∃ t, t < 2 ∧ f t = x} 2 := by
  constructor
  · -- Show 2 is attained by f(x) with some x < 2, here x = 1
    use 1
    constructor
    · norm_num
    · -- Show f(1) = 2
      rw [hf]
      norm_num
  · -- Show that 2 is the least element
    intro x hx
    rcases hx with ⟨t, ht, heq⟩
    have ht2 : 2 - t > 0 := by linarith
    rw [hf] at heq
    have eq1 : (5 - 4 * t + t^2) / (2 - t) = x := heq
    have h2 : 5 - 4 * t + t^2 = x * (2 - t) := by
      field_simp [(show (2 - t : ℝ) ≠ 0 from by linarith)] at eq1
      linarith
    have h3 : (t - 1) ^ 2 ≥ 0 := by
      apply sq_nonneg
    have h4 : 5 - 4 * t + t^2 ≥ 2 * (2 - t) := by
      nlinarith [h3]
    have h5 : 5 - 4 * t + t^2 = x * (2 - t) := by
      linarith [h2]
    nlinarith [show (2 - t : ℝ) > 0 by linarith [ht]]