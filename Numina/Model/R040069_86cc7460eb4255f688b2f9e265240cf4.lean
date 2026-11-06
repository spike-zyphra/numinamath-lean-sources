import Mathlib

open Real Set
open scoped Real

theorem calculus_17274 (A : Real) (hA : A ∈ Ioo (π / 2) π) (hA1 : sin A = 3 / 4) :
    cos A = -sqrt 7 / 4 := by
  rcases hA with ⟨h1, h2⟩
  have h3 : cos A < 0 := by
    have h4 : cos A < 0 := by
      apply cos_neg_of_pi_div_two_lt_of_lt
      all_goals
        linarith [h1, h2, Real.pi_pos]
    linarith
  have h5 : cos A ^ 2 = 1 - sin A ^ 2 := by
    rw [← Real.cos_sq_add_sin_sq A]
    linarith
  rw [hA1] at h5
  have h6 : cos A ^ 2 = 7 / 16 := by
    rw [h5]
    norm_num
  have h7 : cos A = -Real.sqrt 7 / 4 := by
    have h8 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
    have h9 : cos A ^ 2 - (7 / 16) = 0 := by
      linarith [h6]
    have h10 : (cos A + Real.sqrt 7 / 4) * (cos A - Real.sqrt 7 / 4) = 0 := by
      nlinarith [h8, h9]
    cases' (mul_eq_zero.1 h10) with h11 h12
    · -- Case 1: cos A + sqrt 7 / 4 = 0
      have h77 : cos A = -Real.sqrt 7 / 4 := by
        linarith
      exact h77
    · -- Case 2: cos A - sqrt 7 / 4 = 0
      have h77 : cos A > 0 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (7 : Real) by norm_num), Real.sq_sqrt (show (0 : Real) ≤ (7 : Real) by norm_num)]
      linarith [h3, h77]
  rw [h7]
  all_goals
    ring_nf <;> norm_num