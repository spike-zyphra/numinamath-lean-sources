import Mathlib

theorem algebra_20015 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h1 : ∃ r, a = 6 * r ∧ b = a * r) (h2 : ∃ r, a = 1 / b * r ∧ 54 = a * r) :
    a = 3 * Real.sqrt 2 := by
  rcases h1 with ⟨r1, ha1, hb1⟩
  rcases h2 with ⟨r2, ha2, h3⟩
  have eq1 : b = 6 * r1 ^ 2 := by
    have eq2 : a = 6 * r1 := by
      linarith
    rw [eq2] at hb1
    nlinarith
  have eq2 : a ^ 2 = 6 * b := by
    have eq3 : a = 6 * r1 := by 
      linarith
    have eq4 : b = 6 * r1 ^ 2 := by
      nlinarith
    have eq5 : a ^ 2 = 36 * r1 ^ 2 := by
      rw [eq3]
      nlinarith
    nlinarith [eq5, eq4]
  have eq3 : r2 = a * b := by 
    have h4 : b ≠ 0 := by 
      linarith
    field_simp [h4] at ha2 ⊢
    nlinarith
  have eq4 : a ^ 2 * b = 54 := by
    rw [show r2 = a * b by linarith [eq3]] at h3
    linarith
  have eq5 : b ^ 2 = 9 := by
    nlinarith [eq2, eq4]
  have eq6 : b = 3 := by
    nlinarith [eq5, sq_pos_of_pos hb]
  have eq7 : a ^ 2 = 18 := by
    nlinarith [eq2, eq6]
  have eq8 : a = Real.sqrt 18 := by
    have eq9 : a ^ 2 = 18 := by
      linarith [eq7]
    have : a = Real.sqrt 18 := by 
      rw [←eq9]
      field_simp
    linarith
  have eq10 : Real.sqrt 18 = 3 * Real.sqrt 2 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [eq10] at eq8 
  linarith