import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_142175 {f : ℝ → ℝ}
  (hf : f = λ x => (x^4 + x^2 + 5)/(x^2 + 1)^2) :
  IsGreatest (range f) 5 ∧ IsLeast (range f) 0.95 :=
by
  constructor
  · -- First, we prove that 5 is greatest in the range of f.
    constructor
    · -- Show 5 is attained by f.
      use 0
      simp [hf]
      all_goals norm_num
    · -- Show 5 is greatest
      intro y
      rintro ⟨x, hx⟩
      simp [hf] at hx
      have h1 : (x^4 + x^2 + 5) / (x^2 + 1) ^ 2 ≤ 5 := by
        have h2 : (x^2 + 1 : ℝ) > 0 := by
          nlinarith [sq_nonneg x]
        have h3 : (x ^ 4 + x ^ 2 + 5 : ℝ) ≤ 5 * (x ^ 2 + 1) ^ 2 := by
          nlinarith [sq_nonneg (x ^ 2 - 0), sq_nonneg (x ^ 2 - 3), sq_nonneg (x ^ 2 + 1), sq_nonneg (x ^ 2 - 9)]
        have h4 : (x^4 + x^2 + 5 : ℝ) / (x^2 + 1) ^ 2 ≤ 5 := by
          have h5 : (x ^ 2 + 1 : ℝ) ^ 2 > 0 := by positivity
          apply (div_le_iff₀ (by positivity)).mpr
          nlinarith [h3]
        exact h4
      linarith
  · -- Now, prove that 0.95 is the least in the range of f
    constructor
    · -- Show 0.95 is attained by f.
      use (3 : ℝ)
      simp [hf]
      all_goals norm_num
    · -- Show 0.95 is the least
      intro y
      rintro ⟨x, hx⟩
      simp [hf] at hx
      have h2 : (x^4 + x^2 + 5) / (x ^ 2 + 1) ^ 2 ≥ (0.95 : ℝ) := by
        have hx2_pos : (x ^ 2 + 1 : ℝ) ^ 2 > 0 := by positivity
        have h3 : (x ^ 4 + x ^ 2 + 5 : ℝ) ≥ (0.95 : ℝ) * (x ^ 2 + 1) ^ 2 := by
          nlinarith [sq_nonneg (x ^ 2 - 3), sq_nonneg (x ^ 2 - 0), sq_nonneg (x ^ 2 - 3), sq_nonneg (x ^ 2 + 1), sq_nonneg (x ^ 2 - 9), sq_nonneg (x), sq_nonneg (x - 3), sq_nonneg (x + 3)]
        have h4 : (x^4 + x^2 + 5 : ℝ) / (x ^ 2 + 1) ^ 2 ≥ (0.95 : ℝ) := by
          have h5 : (x ^ 2 + 1 : ℝ) ^ 2 > 0 := by positivity
          apply (le_div_iff₀ (by positivity)).mpr
          linarith [h3]
        exact h4
      linarith