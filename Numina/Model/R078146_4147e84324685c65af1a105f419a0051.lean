import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_250005 (a : ℝ) :
  (∀ x : ℝ, arctan (sqrt (x^2 + x + 13/4)) ≥ π/3 - a) ↔ a ≥ 0 := by
  constructor
  · -- Assuming that for all real numbers x, arctan sqrt(x^2 + x + 13/4) ≥ π/3 - a, we need to prove a ≥ 0.
    intro h
    have h1 := h (-1/2)
    have h2 : sqrt ((-1/2 : ℝ)^2 + (-1/2 : ℝ) + 13/4) = Real.sqrt 3 := by
      norm_num
    have h3 : arctan (sqrt ((-1/2 : ℝ)^2 + (-1/2 : ℝ) + 13/4)) = Real.pi / 3 := by
      rw [h2]
      have h4 : arctan (Real.sqrt 3) = Real.pi / 3 := by
        have h5 : (Real.sqrt 3 : ℝ) = Real.tan (Real.pi / 3) := by
          rw [Real.tan_pi_div_three]
        rw [h5]
        have h6 : arctan (Real.tan (Real.pi / 3)) = Real.pi / 3 := by
          apply Real.arctan_tan
          all_goals linarith [Real.pi_pos]
        rw [h6]
      rw [h4]
    linarith [h1, h3]
  · -- Assuming a ≥ 0, we need to prove that for all real numbers x, arctan sqrt(x^2 + x + 13/4) ≥ π/3 - a.
    intro ha x
    have h1 : x^2 + x + 13/4 ≥ 3 := by
      nlinarith [sq_nonneg (x + 1 / 2)]
    have h2 : sqrt (x^2 + x + 13 / 4) ≥ Real.sqrt 3 := Real.sqrt_le_sqrt (h1)
    have h3 : arctan (sqrt (x^2 + x + 13 / 4)) ≥ arctan (Real.sqrt 3) := by
      apply Real.arctan_le_arctan
      all_goals linarith [h2]
    have h4 : arctan (Real.sqrt 3) = Real.pi / 3 := by
      have h5 : (Real.sqrt 3 : ℝ) = Real.tan (Real.pi / 3) := by
        rw [Real.tan_pi_div_three]
      rw [h5]
      have h6 : arctan (Real.tan (Real.pi / 3)) = Real.pi / 3 := by
        apply Real.arctan_tan
        all_goals linarith [Real.pi_pos]
      rw [h6]
    linarith [h3, h4, ha]