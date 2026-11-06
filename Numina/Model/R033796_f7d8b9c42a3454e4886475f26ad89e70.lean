import Mathlib

theorem algebra_207356 {a : ℕ → ℝ} (P : ℝ → ℝ)
    (hP : ∀ x, P x = x^4 + a 3 * x^3 + a 2 * x^2 + a 1 * x + a 0)
    (hP1 : P 1 = 1) (hP2 : P 2 = 2) (hP3 : P 3 = 3) (hP4 : P 4 = 4) :
    Real.sqrt (P 13 - 12) = 109 := by 
  have eq1 := hP 1
  have eq2 := hP 2
  have eq3 := hP 3
  have eq4 := hP 4
  norm_num at eq1 eq2 eq3 eq4
  have eq5 : 7 * a 3 + 3 * a 2 + a 1 = -14 := by
    linarith
  have eq6 : 26 * a 3 + 8 * a 2 + 2 * a 1 = -78 := by
    linarith
  have eq7 : 63 * a 3 + 15 * a 2 + 3 * a 1 = -252 := by
    linarith
  have eq8 : 12 * a 3 + 2 * a 2 = -50 := by
    linarith
  have eq9 : 6 * a 3 + a 2 = -25 := by
    linarith
  have ha3 : a 3 = -10 := by
    nlinarith 
  have ha2 : a 2 = 35 := by
    rw [ha3] at eq9
    linarith
  have ha1 : a 1 = -49 := by
    rw [ha3, ha2] at eq5
    linarith
  have ha0 : a 0 = 24 := by
    rw [ha3, ha2, ha1] at eq1
    linarith
  have h7 : Real.sqrt (P 13 - 12) = 109 := by 
    have h8 : P 13 = 13 ^ 4 + a 3 * 13 ^ 3 + a 2 * 13 ^ 2 + a 1 * 13 + a 0 := by 
      specialize hP 13 
      simpa using hP 
    have h9 : P 13 - 12 = 11881 := by 
      rw [h8]
      rw [ha3, ha2, ha1, ha0]
      norm_num 
    rw [h9]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
  exact h7