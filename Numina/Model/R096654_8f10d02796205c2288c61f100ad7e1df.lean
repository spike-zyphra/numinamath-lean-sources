import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_224273 (f : ℝ → ℝ) (hf : f = λ x => (1 + x^2) / (1 + x)) :
  IsLeast {y | ∃ x, 0 ≤ x ∧ f x = y} (2 * (sqrt 2 - 1)) := by
  constructor
  · -- Show 2*(sqrt 2 -1) is attainable, by x = sqrt 2 -1
    use Real.sqrt 2 - 1
    constructor
    · -- Show sqrt 2 -1 >= 0
      have h2 : 1 < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
      have h1 : 0 ≤ Real.sqrt 2 - 1 := by linarith [Real.sqrt_nonneg 2]
      linarith
    · -- Show f (sqrt 2 - 1) = 2*(sqrt 2 -1)
      rw [hf]
      have h3 : Real.sqrt 2 > 1 := by
        have h4 : 1 < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
        linarith
      field_simp [show Real.sqrt 2 > 0 by positivity]
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · -- Show 2*(sqrt 2 -1) is the least
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    have h1 : f x = (1 + x^2) / (1 + x) := by
      rw [hf]
    rw [h1] at hfx
    have h2 : 1 + x ≥ 0 := by linarith
    have h4 : (1 + x ^ 2) ≥ 2 * (sqrt 2 - 1) * (1 + x) := by
      nlinarith [sq_nonneg (x - (Real.sqrt 2 - 1)), sq_nonneg (x - (Real.sqrt 2 - 1)), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h5 : (1 + x ^ 2) / (1 + x) ≥ 2 * (sqrt 2 - 1) := by
      apply (le_div_iff₀ (show (1 + x) > 0 by linarith)).mpr
      linarith
    linarith