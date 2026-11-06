import Mathlib

theorem algebra_173941 {x y z : ℝ} (h₀ : x ≠ y) (h₁ : y ≠ z) (h₂ : z ≠ x)
    (h₃ : x^2 + y^2 = -x + 3 * y + z) (h₄ : y^2 + z^2 = x + 3 * y - z)
    (h₅ : x^2 + z^2 = 2 * x + 2 * y - z) :
    (x, y, z) = (-3 / 2, 5 / 2, -1 / 2) ∨ (x, y, z) = (0, 1, -2) := by

  have eq1 : (x - z) * (x + z + 2) = 0 := by
    nlinarith
  have eq2 : x + z + 2 = 0 := by
    apply_fun (fun w => w / (x - z)) at eq1
    field_simp [(show x - z ≠ 0 by intro h; apply h₂; linarith)] at eq1
    <;> nlinarith
  
  have eq3 : (x - y) * (x + y - 1) = 0 := by
    nlinarith
  
  have eq4 : x + y = 1 := by
    apply (mul_right_inj' (show (x - y : ℝ) ≠ 0 by intro h; apply h₀; linarith)).mp
    linarith
  
  have eq5 : z = -2 - x := by
    linarith [eq2]

  have eq6 : y = 1 - x := by 
    linarith [eq4]

  rw [show z = -2 - x by linarith [eq5]] at h₅
  rw [show y = 1 - x by linarith [eq6]] at h₅

  have eq7 : x * (2 * x + 3) = 0 := by
    nlinarith
  
  cases' (mul_eq_zero.mp eq7) with h8 h9
  · -- Case x = 0
    have hx : x = 0 := by
      linarith
    have hy : y = 1 := by 
      rw [hx] at eq6
      linarith
    have hz : z = -2 := by 
      rw [hx] at eq5
      linarith
    right
    simp [hx, hy, hz]
  
  · -- Case 2x + 3 = 0
    have hx : x = -3 / 2 := by
      linarith
    have hy : y = 5 / 2 := by
      rw [hx] at eq6
      linarith
    have hz : z = -1 / 2 := by 
      rw [hx] at eq5
      linarith
    left
    simp [hx, hy, hz]