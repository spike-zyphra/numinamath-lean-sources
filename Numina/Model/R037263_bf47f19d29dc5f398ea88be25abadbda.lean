import Mathlib

theorem algebra_29 {x y z : ℝ}
    (hx : x ≠ -1) (hy : y ≠ -1) (hz : z ≠ -1) (h1 : 1 / (1 + x) = y) (h2 : 1 / (1 + y) = z) (h3 : 1 / (1 + z) = x) :
    x = (Real.sqrt 5 - 1) / 2 ∧ y = (Real.sqrt 5 - 1) / 2 ∧ z = (Real.sqrt 5 - 1) / 2 ∨
    x = (-Real.sqrt 5 - 1) / 2 ∧ y = (-Real.sqrt 5 - 1) / 2 ∧ z = (-Real.sqrt 5 - 1) / 2 := by
  have eq1 : 1 + x ≠ 0 := by
    intro h
    apply hx
    linarith
  have eq2 : 1 + y ≠ 0 := by
    intro h
    apply hy
    linarith
  have eq3 : 1 + z ≠ 0 := by
    intro h
    apply hz
    linarith
  have eq4 : 1 = y * (1 + x) := by
    field_simp [eq1] at h1
    linarith
  have eq5 : 1 = z * (1 + y) := by 
    field_simp [eq2] at h2
    linarith
  have eq6 : 1 = x * (1 + z) := by
    field_simp [eq3] at h3
    linarith
  have h10 : x^2 + x - 1 = 0 := by
    nlinarith [sq_pos_of_ne_zero (show 1 + x ≠ 0 by assumption), sq_pos_of_ne_zero (show 1 + y ≠ 0 by assumption), sq_pos_of_ne_zero (show 1 + z ≠ 0 by assumption)]
  have h11 : x = (Real.sqrt 5 - 1) / 2 ∨ x = (-Real.sqrt 5 - 1) / 2 := by
    have h12 : x^2 + x - 1 = 0 := h10
    have h13 : (x - (Real.sqrt 5 - 1) / 2) * (x - (-Real.sqrt 5 - 1) / 2) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp h13) with h14 h15
    · left
      linarith
    · right
      linarith
  cases h11 with
  | inl hx1 =>
    have hy1 : y = (Real.sqrt 5 - 1) / 2 := by 
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), hx1, sq_pos_of_ne_zero (show 1 + x ≠ 0 by assumption)]
    have hz1 : z = (Real.sqrt 5 - 1) / 2 := by 
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), hx1, sq_pos_of_ne_zero (show 1 + x ≠ 0 by assumption)]
    left
    constructor
    · exact hx1
    constructor 
    · exact hy1 
    · exact hz1
  | inr hx2 =>
    have hy2 : y = (-Real.sqrt 5 - 1) / 2 := by
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), hx2, sq_pos_of_ne_zero (show 1 + x ≠ 0 by assumption)]
    have hz2 : z = (-Real.sqrt 5 - 1) / 2 := by 
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), hx2, sq_pos_of_ne_zero (show 1 + x ≠ 0 by assumption)]
    right
    constructor
    · exact hx2
    constructor 
    · exact hy2 
    · exact hz2