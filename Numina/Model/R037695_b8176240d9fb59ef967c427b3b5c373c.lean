import Mathlib

theorem algebra_155847 (f : ℝ → ℝ → ℝ)
    (h₀ : ∀ s t, f s t = (s + 5 - 3 * abs (Real.cos t))^2 + (s - 2 * abs (Real.sin t))^2) :
    IsLeast {x | ∃ s t, x = f s t} 2 := by
  constructor
  · -- Show that 2 is in the set.
    use -1, 0
    rw [h₀]
    have h1 : Real.cos (0 : ℝ) = 1 := Real.cos_zero
    have h2 : Real.sin (0 : ℝ) = 0 := Real.sin_zero
    simp [h1, h2, abs_of_nonneg, abs_of_nonneg]
    all_goals norm_num [h1, h2]
  · -- Show that 2 is the least in the set.
    intro x hx
    rcases hx with ⟨s, t, hx⟩
    rw [h₀] at hx
    have h3 : 0 ≤ (abs (Real.cos t) : ℝ) := abs_nonneg (Real.cos t)
    have h4 : 0 ≤ (abs (Real.sin t) : ℝ) := abs_nonneg (Real.sin t)
    have h5 : (abs (Real.cos t) : ℝ) ^ 2 + (abs (Real.sin t) : ℝ) ^ 2 = 1 := by
      have h1 : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := Real.cos_sq_add_sin_sq t
      have h2 : abs (Real.cos t) ^ 2 = Real.cos t ^ 2 := by
        cases' abs_cases (Real.cos t) with hc hc
        · -- cos t ≥ 0
          nlinarith
        · -- cos t < 0
          nlinarith
      have h3 : abs (Real.sin t) ^ 2 = Real.sin t ^ 2 := by
        cases' abs_cases (Real.sin t) with hs1 hs1
        · -- sin t ≥ 0
          nlinarith
        · -- sin t < 0
          nlinarith
      nlinarith [h1, h2, h3]
    nlinarith [sq_nonneg ((s + 5 - 3 * abs (Real.cos t)) + (s - 2 * abs (Real.sin t))), sq_nonneg ((s + 5 - 3 * abs (Real.cos t)) - (s - 2 * abs (Real.sin t))), sq_nonneg (abs (Real.cos t) - 1), sq_nonneg (abs (Real.sin t) - 1), Real.sin_sq_add_cos_sq t, h5, abs_nonneg (Real.cos t), abs_nonneg (Real.sin t)]