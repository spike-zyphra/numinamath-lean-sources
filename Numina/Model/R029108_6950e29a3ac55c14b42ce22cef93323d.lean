import Mathlib

open Real

theorem algebra_22236 {x : ℝ} (hx : x = 1 / (2 - 1 / (2 - x))) : x = 1 := by
  have h1 : 2 - x ≠ 0 := by
    by_contra h
    have eq1 : x = 2 := by linarith
    rw [eq1] at hx
    norm_num at hx

  have h3 : x ≠ 3 / 2 := by
    by_contra h
    have eq1 : x = 3 / 2 := by linarith
    have eq2 : (2 - x) = 1 / 2 := by 
      rw [eq1]
      norm_num
    have eq3 : 1 / (2 - x) = 2 := by
      rw [eq2]
      norm_num
    have eq4 : (2 - 1 / (2 - x)) = (0 : ℝ) := by
      rw [eq3]
      norm_num
    rw [eq4] at hx
    norm_num [eq1] at hx

  have h2 : (2 - 1 / (2 - x)) ≠ 0 := by 
    by_contra h_eq
    have h4 : 2 - 1 / (2 - x) = 0 := by
      linarith [h_eq]
    have eq1 : x = 3 / 2 := by
      field_simp [h1] at h4
      linarith
    exfalso
    tauto
  
  have eq1 : x = (2 - x) / (2 * (2 - x) - 1) := by 
    field_simp [h1, h2] at hx ⊢
    <;> nlinarith [h1]

  have h4 : 2 * (2 - x) - 1 ≠ 0 := by
    by_contra h
    have eq1 : (2 * (2 - x) - 1) = (0 : ℝ) := by
      linarith [h]
    have eq2 : x = 3 / 2 := by 
      nlinarith 
    exfalso 
    tauto 
  have eq2 : x * (2 * (2 - x) - 1) = 2 - x := by
    have hx1 : x = (2 - x) / (2 * (2 - x) - 1) := eq1
    field_simp [h4] at hx1 ⊢
    <;> nlinarith [hx1, h1]

  have eq5 : (x -1)^2 = 0 := by 
    nlinarith [eq2]

  have eq7 : x -1 =0 := by 
    apply pow_eq_zero 
    exact eq5 
  linarith [eq7]