import Mathlib

theorem algebra_197899 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h₁ : x + 1 / y + y / x = 3) (h₂ : y + 1 / x + x / y = 3) :
    (x, y) = (1, 1) := by

  have eq1 : x^2 * y + x + y^2 = 3 * x * y := by
    have eq3 : (x + 1 / y + y / x) * (x * y) = 3 * (x * y) := by 
      rw [h₁]
    have eq4 : (x + 1 / y + y / x) * (x * y) = x^2 * y + x + y^2 := by 
      field_simp [hx, hy]
      <;> ring 
    rw [eq4] at eq3 
    linarith
  
  have eq2 : x * y^2 + y + x^2 = 3 * x * y := by 
    have eq5 : (y + 1 / x + x / y) * (x * y) = 3 * (x * y) := by 
      rw [h₂]
    have eq6 : (y + 1 / x + x / y) * (x * y) = x * y^2 + y + x^2 := by 
      field_simp [hx, hy]
      <;> ring 
    rw [eq6] at eq5 
    linarith

  have eq3 : (x - y) * (x * y + 1 - (x + y)) = 0 := by 
    nlinarith

  cases' (mul_eq_zero.mp eq3) with h4 h5
  · -- Case x - y = 0, so x = y
    have h6 : x = y := by linarith
    rw [show y = x by linarith [h6]] at eq1 
    have eq4 : x * (x - 1) ^ 2 = 0 := by 
      nlinarith
    cases' (mul_eq_zero.mp eq4) with eq6 eq7
    · -- Case x = 0
      exfalso
      apply hx
      linarith 
    · -- Case (x - 1)^2 = 0 
      have hx1 : x = 1 := by 
        nlinarith 
      have hy1 : y = 1 := by 
        nlinarith [h6, hx1] 
      simp [Prod.ext_iff, hx1, hy1]
  
  · -- Case x * y + 1 - (x + y) = 0 
    have h7 : (x - 1) * (y - 1) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- Case x - 1 = 0, so x = 1 
      have hx1 : x = 1 := by linarith 
      rw [hx1] at eq1 
      have eq8 : y^2 - 2 * y + 1 = 0 := by 
        nlinarith 
      have hy1 : y = 1 := by 
        nlinarith 
      simp [Prod.ext_iff, hx1, hy1]
    · -- Case y - 1 = 0, so y = 1 
      have hy1 : y = 1 := by linarith 
      rw [hy1] at eq1 
      have eq9 : x^2 - 2 * x + 1 = 0 := by 
        nlinarith 
      have hx1 : x = 1 := by 
        nlinarith 
      simp [Prod.ext_iff, hx1, hy1]