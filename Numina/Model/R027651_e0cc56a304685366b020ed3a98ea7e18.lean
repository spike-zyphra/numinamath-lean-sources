import Mathlib

open Real Set
open scoped Real

theorem algebra_323749 (x : Real) (hx : x ∈ Ioo 0 (π / 2)) (h : 2 * sin x ^ 2 + sin x - sin (2 * x) = 3 * cos x) :
    x = π / 3 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : sin (2 * x) = 2 * sin x * cos x := by
    rw [sin_two_mul]
  rw [h1] at h
  have h2 : sin x > 0 := by 
    apply sin_pos_of_pos_of_lt_pi
    linarith [hx1, hx2, Real.pi_pos]
    linarith [hx1, hx2, Real.pi_pos]
  have h3 : cos x > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [hx1, hx2, Real.pi_pos]
  have h4 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have eq1 : 2 * sin x ^ 2 + sin x - 2 * sin x * cos x - 3 * cos x = 0 := by
    linarith
  have eq3 : sin x = Real.sqrt 3 / 2 := by
    nlinarith [sq_nonneg (sin x - Real.sqrt 3 / 2), sq_nonneg (cos x - 1 / 2), 
              Real.sqrt_pos.mpr (show (0 : Real) < (3 : Real) by norm_num), 
              Real.sq_sqrt (show (0 : Real) ≤ (3 : Real) by norm_num), 
              sq_pos_of_pos h2, sq_pos_of_pos h3, 
              mul_pos h2 h3, 
              sq_nonneg (sin x ^ 2 - 3 / 4), sq_nonneg (cos x ^ 2 - 1 / 4)
            ]
  have eq4 : cos x = 1 / 2 := by
    have h5 : sin x ^ 2 + cos x ^ 2 = 1 := h4
    rw [eq3] at h5
    nlinarith [Real.sqrt_pos.mpr (show (0 : Real) < (3 : Real) by norm_num), Real.sq_sqrt (show (0 : Real) ≤ (3 : Real) by norm_num)]
  have eq5 : x = Real.arcsin (sin x) := by
    rw [Real.arcsin_sin]
    all_goals
      nlinarith [Real.pi_pos, hx1, hx2]
  rw [eq3] at eq5
  have eq6 : x = Real.arcsin (Real.sqrt 3 / 2) := eq5
  have eq7 : Real.arcsin (Real.sqrt 3 / 2) = Real.pi / 3 := by
    have h8 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := by
      exact sin_pi_div_three
    have h9 : Real.arcsin (Real.sin (Real.pi / 3)) = Real.pi / 3 := by
      rw [Real.arcsin_sin]
      all_goals
        nlinarith [Real.pi_pos]
    rw [h8] at h9
    linarith
  rw [eq7] at eq6
  linarith