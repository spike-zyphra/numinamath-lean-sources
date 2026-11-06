import Mathlib

theorem algebra_267673 {x y a b : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x * y = b) (h : 1 / x ^ 2 + 1 / y ^ 2 = a) :
    (x + y) ^ 2 = b * (a * b + 2) := by

  have eq1 : 1 / x ^ 2 + 1 / y ^ 2 = (x^2 + y^2) / (x * y) ^ 2 := by
    field_simp [hx, hy]
    <;> ring
  have eq3 : (x^2 + y^2) / (x * y) ^ 2 = a := by
    have eq4 : 1 / x^2 + 1 / y^2 = (x^2 + y^2) / (x * y) ^ 2 := eq1
    linarith [h, eq4]

  have h_eq2 : x^2 + y^2 = a * b^2 := by
    have eq4 : (x * y) ^ 2 = b ^ 2 := by 
      rw [hxy]
      all_goals ring
    have h10 : (x ^ 2 + y ^ 2) / (x * y) ^ 2 = a := eq3
    have h11 : x ^ 2 + y ^ 2 = a * ((x * y) ^ 2) := by 
      have h5 : x * y ≠ 0 := by
        apply mul_ne_zero 
        exact hx 
        exact hy 
      have h8 : (x * y) ^ 2 ≠ 0 := by
        apply pow_ne_zero 2 
        exact h5
      have h9 : (x ^ 2 + y ^ 2) / (x * y) ^ 2 = a := h10
      field_simp [h8] at h9 ⊢ 
      all_goals linarith 
    rw [eq4] at h11 
    linarith
  
  have eq3 : (x + y) ^ 2 = x^2 + y^2 + 2 * (x * y) := by 
    ring 
  rw [eq3] 
  rw [h_eq2] 
  have eq4 : 2 * (x * y) = 2 * b := by 
    rw [hxy] 
    all_goals ring 
  rw [eq4] 
  all_goals 
    ring_nf <;> nlinarith