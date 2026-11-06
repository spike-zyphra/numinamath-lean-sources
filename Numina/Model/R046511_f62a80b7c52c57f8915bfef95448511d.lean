import Mathlib

theorem algebra_239283 {x y z : ℝ} (h₀ : z / (x + y) = 2) (h₁ : y / (x + z) = 3) :
    z / (y + z) = 8 / 17 := by

  have h2 : x + y ≠ 0 := by
    by_contra h
    have eq : z / (x + y) = 0 := by 
      rw [h]
      norm_num
    linarith [h₀, eq]
  
  have h3 : x + z ≠ 0 := by
    by_contra h
    have eq : y / (x + z) = 0 := by 
      rw [h]
      norm_num
    linarith [h₁, eq]

  have eq1 : z = 2 * (x + y) := by
    have h : z / (x + y) = 2 := h₀
    field_simp [h2] at h ⊢
    linarith
  
  have eq2 : y = 3 * (x + z) := by
    have h : y / (x + z) = 3 := h₁
    field_simp [h3] at h ⊢
    linarith
  
  have h4 : y + z ≠ 0 := by
    by_contra h
    have eq5 : y = 0 := by
      nlinarith [h, eq1, eq2]
    have eq6 : z = 0 := by
      nlinarith [eq1, eq5]
    have eq7 : x + z = 0 := by
      nlinarith [eq6, eq5]
    have h9 : y / (x + z) = 0 := by 
      rw [eq7]
      norm_num
    linarith [h₁, h9]
  
  have h4' : y ≠ 0 := by
    by_contra h
    have eq5 : z = 0 := by
      nlinarith [eq1, h]
    have eq6 : x + z = 0 := by
      nlinarith [eq5, h]
    have h9 : y / (x + z) = 0 := by 
      rw [eq6]
      norm_num
    linarith [h₁, h9]

  have eq3 : z = 8 / 9 * y := by
    nlinarith [eq1, eq2]

  have eq7 : y + z = (17 / 9) * y := by 
    nlinarith [eq3]
  
  have eq6 : z = 8 / 9 * y := eq3

  rw [eq7, eq6]
  have h7 : y ≠ 0 := h4'
  field_simp [h7]
  <;> nlinarith