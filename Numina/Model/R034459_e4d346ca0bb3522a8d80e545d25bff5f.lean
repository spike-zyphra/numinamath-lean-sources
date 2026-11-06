import Mathlib

theorem algebra_201515 {x y z : ℝ} (h₀ : x ≠ 0) (h₁ : y ≠ 0) (h₂ : z ≠ 0)
    (h₃ : 1/x + 2/y + 3/z = 0) (h₄ : 1/x - 6/y - 5/z = 0) :
    x/y + y/z + z/x = -1 := by 
  have eq1 : y * z + 2 * x * z + 3 * x * y = 0 := by
    have h3' : 1 / x + 2 / y + 3 / z = 0 := h₃
    field_simp [h₀, h₁, h₂] at h3' ⊢
    linarith
  have eq2 : y * z - 6 * x * z - 5 * x * y = 0 := by
    have h4' : 1 / x - 6 / y - 5 / z = 0 := h₄
    field_simp [h₀, h₁, h₂] at h4' ⊢
    linarith
  have eq3 : x * (y + z) = 0 := by 
    nlinarith [eq1, eq2]
  have eq4 : y + z = 0 := by
    apply (mul_left_inj' h₀).mp
    linarith
  have h5 : z = -y := by linarith
  rw [h5] at eq2
  have eq5 : y * (y - x) = 0 := by
    nlinarith [eq2]
  cases' (mul_eq_zero.mp eq5) with hy1 hy2
  · -- y = 0 is a contradiction
    exfalso
    apply h₁
    linarith
  · -- y - x = 0
    have eq6 : y = x := by linarith
    have eq7 : z = -x := by
      linarith [eq6, h5]
    have eq8 : x / y = 1 := by
      rw [show y = x by linarith [eq6]]
      field_simp [h₀]
    have eq9 : y / z = -1 := by
      rw [show z = -x by linarith [eq7]]
      rw [show y = x by linarith [eq6]]
      field_simp [h₀]
    have eq10 : z / x = -1 := by 
      rw [show z = -x by linarith [eq7]]
      field_simp [h₀]
    rw [eq8, eq9, eq10]
    all_goals norm_num