import Mathlib

open Real Set

theorem algebra_11513 (f : ℝ → ℝ → ℝ)
    (h₀ : ∀ x y, f x y = (x + 1 - cos y)^2 + (x - 1 + sin y)^2) :
    IsLeast {z | ∃ x y, z = f x y} (3 - 2 * sqrt 2) := by
  constructor
  · -- Show that 3 - 2*sqrt 2 is in the set
    use 0, Real.pi / 4
    rw [h₀ 0 (Real.pi / 4)]
    have h1 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      exact cos_pi_div_four
    have h2 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      exact sin_pi_div_four
    rw [h1, h2]
    nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  · -- Show that 3 - 2*sqrt 2 is the minimum
    intro z hz
    rcases hz with ⟨x, y, hz⟩
    rw [hz]
    rw [h₀ x y]
    have h6 : (x + 1 - cos y) ^ 2 + (x - 1 + sin y) ^ 2 ≥ 0 := by positivity
    have h7 : Real.sqrt 2 ^ 2 = 2 := by rw [Real.sq_sqrt]; linarith
    have h5 : Real.sqrt 2 ≥ 0 := by positivity
    have h8 : 3 - 2 * Real.sqrt 2 ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    have h41 : (x + 1 - cos y) ^ 2 + (x - 1 + sin y) ^ 2 ≥ 3 - 2 * Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2, sq_nonneg (x - (cos y - sin y) / 2 ), sq_nonneg (sin y - cos y), Real.sin_sq_add_cos_sq y, sq_nonneg (sin y + cos y - Real.sqrt 2), sq_nonneg (sin y + cos y + Real.sqrt 2), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    nlinarith