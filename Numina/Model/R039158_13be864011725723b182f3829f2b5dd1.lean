import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_62172 (f : ℝ → ℝ → ℝ)
  (h₀ : ∀ x y, f x y = x + y) :
  IsGreatest {z | ∃ x y, z = f x y ∧ x ^ 2 + y ^ 2 ≤ 1} (f (1 / sqrt 2) (1 / sqrt 2)) := by
  constructor
  · -- Show that f (1 / sqrt 2) (1 / sqrt 2) is in the set
    use 1 / sqrt 2, 1 / sqrt 2
    constructor
    · -- Show that z = f (1 / sqrt 2) (1 / sqrt 2)
      rfl
    · -- Show that (1 / sqrt 2) ^ 2 + (1 / sqrt 2) ^ 2 <=1
      have h1 : (1 / sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
        rw [div_pow]
        have h2 : sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        field_simp [h2]
        <;> linarith
      linarith [h1, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
  · -- Show that f (1 / sqrt 2) (1 / sqrt 2) is greatest in the set
    intro z hz
    rcases hz with ⟨x, y, h_eq, hxy⟩
    rw [h₀ x y] at h_eq
    have h1 : f (1 / sqrt 2) (1 / sqrt 2) = 1 / sqrt 2 + 1 / sqrt 2 := by
      apply h₀
    have h4 : x + y ≤ Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (x - y), sq_nonneg (x + y - Real.sqrt 2), sq_nonneg (x - 1 / Real.sqrt 2), sq_nonneg (y - 1 / Real.sqrt 2), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2), sq_nonneg (x^2 + y^2 - 1)]
    have h6 : z ≤ f (1 / sqrt 2) (1 / sqrt 2) := by
      -- We have equality from `h1` and bound on x+y from `h4`, so we can establish:
      have h7 : z = x + y := by linarith [h_eq]
      have h8 : x + y ≤ Real.sqrt 2 := h4
      have h9 : f (1 / sqrt 2) (1 / sqrt 2) = Real.sqrt 2 := by
        rw [h1]
        have h2 : 1 / sqrt 2 + 1 / sqrt 2 = Real.sqrt 2 := by
          have h5 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
          have h8 : Real.sqrt 2 > 0 := by positivity
          field_simp [h5, h8]
          <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), h5]
        linarith
      linarith [h7, h8, h9]
    linarith