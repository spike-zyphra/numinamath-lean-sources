import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_204036 (f : ℝ → ℝ)
  (h₀ : ∀ x, 0 < x → f x = x^2 + 2 * x + 6 / x + 9 / x^2 + 4) :
  IsLeast {y | ∃ x, 0 < x ∧ f x = y} (10 + 4 * sqrt 3) := by
  constructor
  · -- Show that 10 + 4 * sqrt 3 is in the set
    use Real.sqrt 3
    constructor
    · -- Show that sqrt 3 > 0
      positivity
    · -- Show that f (sqrt 3) = 10 + 4 * sqrt 3
      have h1 : Real.sqrt 3 > 0 := by positivity
      have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by linarith)
      have h3 : f (Real.sqrt 3) = Real.sqrt 3^2 + 2 * Real.sqrt 3 + 6 / Real.sqrt 3 + 9 / Real.sqrt 3^2 + 4 := by
        apply h₀
        all_goals linarith [Real.sqrt_pos.mpr (show (3 : ℝ) > (0 : ℝ) by norm_num)]
      rw [h3]
      have h4 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := h2
      have h5 : 6 / Real.sqrt 3 = 2 * Real.sqrt 3 := by
        field_simp [show Real.sqrt 3 ≠ 0 by positivity]
        <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      have h6 : 9 / (Real.sqrt 3 ^ 2) = 3 := by
        rw [h4]
        norm_num
      rw [h5, h6]
      nlinarith [h4, Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)]
  · -- Show that 10 + 4 * sqrt 3 is the least in the set
    intro y hy
    rcases hy with ⟨x, hx, h_eq⟩
    have eq1 : f x = x^2 + 2 * x + 6 / x + 9 / x^2 + 4 := by
      apply h₀
      exact hx
    rw [eq1] at h_eq
    have h7 : x^2 + 2 * x + 6 / x + 9 / x^2 + 4 - (10 + 4 * Real.sqrt 3) ≥ 0 := by
      have hx2 : x > 0 := hx
      have hx_pos1 : x ^ 2 > 0 := by positivity
      have h7' : x ^ 2 + 2 * x + 6 / x + 9 / x ^ 2 + 4 - (10 + 4 * Real.sqrt 3) =
          (x ^ 4 + 2 * x ^ 3 - (6 + 4 * Real.sqrt 3) * x ^ 2 + 6 * x + 9) / (x ^ 2) := by
        field_simp
        ring
      have h8' : x ^ 4 + 2 * x ^ 3 - (6 + 4 * Real.sqrt 3) * x ^ 2 + 6 * x + 9 ≥ 0 := by
        nlinarith [sq_nonneg (x ^ 2 - 3), sq_nonneg (x - Real.sqrt 3), sq_nonneg (x + Real.sqrt 3), sq_nonneg (x ^ 2 - (Real.sqrt 3 : ℝ) ^ 2),
                  sq_nonneg (x * (x - Real.sqrt 3)), sq_nonneg ((x : ℝ) - (Real.sqrt 3 : ℝ) / 2),
                  sq_nonneg (x - 1), sq_nonneg (x * (x + Real.sqrt 3 - Real.sqrt 3)), sq_nonneg (x * (x - Real.sqrt 3)), sq_nonneg (x * Real.sqrt 3 - 3), mul_pos hx2 (show (0 : ℝ) < x by linarith),
                  Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      have h9 : (x ^ 4 + 2 * x ^ 3 - (6 + 4 * Real.sqrt 3) * x ^ 2 + 6 * x + 9) / (x ^ 2) ≥ 0 := by
        apply div_nonneg
        linarith
        all_goals positivity
      linarith [h7']
    linarith [h_eq, h7]