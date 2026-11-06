import Mathlib

theorem algebra_17182: IsGreatest {t : ℝ | (13 * t^2 - 34 * t + 12) / (3 * t - 2) + 5 * t = 6 * t - 1} (5/2) := by
  constructor
  · -- First, we show that 5/2 is a solution to the equation.
    norm_num
  · -- Then, we need to show that any solution t satisfies t ≤ 5/2.
    intro t ht
    have h : (13 * t^2 - 34 * t + 12) / (3 * t - 2) + 5 * t = 6 * t - 1 := ht
    by_cases h1 : 3 * t - 2 = 0
    · -- If 3t - 2 = 0, then t = 2/3, which leads to division by zero.
      have ht2 : t = 2 / 3 := by linarith 
      rw [ht2] at h 
      norm_num at h 
    · -- Assume t ≠ 2/3, can multiply through by 3t - 2.
      have h1' : 3 * t - 2 ≠ 0 := h1
      field_simp [h1'] at h 
      have h2 : 10 * t^2 - 29 * t + 10 = 0 := by 
        nlinarith 
      have h3 : (t - 5 / 2) * (t - 2 / 5) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h3) with h4 h5 
      · -- Case where t = 5/2
        linarith 
      · -- Case where t = 2/5 
        linarith