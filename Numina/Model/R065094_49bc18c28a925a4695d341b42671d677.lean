import Mathlib

theorem algebra_3375 (x y z k : ℝ) (h₀ : x / y = 1 / 2) (h₁ : y / z = 2 / 4)
    (h₂ : 2 * x + 3 * y + 5 * z = 560) (h₃ : 2 * x + 3 * y - 5 * z = k) :
    k = -240 := by
  have h4 : y ≠ 0 := by
    by_contra h
    rw [h] at h₀
    norm_num at h₀
  have h5 : z ≠ 0 := by
    by_contra h
    rw [h] at h₁
    norm_num at h₁
  have h6 : 2 * x = y := by 
    have h7 : y ≠ 0 := h4
    field_simp [h7] at h₀
    linarith
  have h8 : 2 * y = z := by 
    have h9 : z ≠ 0 := h5
    field_simp [h9] at h₁
    linarith
  have h10 : z = 4 * x := by 
    linarith [h6, h8]
  have h11 : x = 20 := by 
    have eq1 : 2 * x + 3 * y + 5 * z = 560 := h₂
    rw [show y = 2 * x by linarith [h6], show z = 4 * x by linarith [h10]] at eq1
    linarith
  have hx : x = 20 := h11
  have hy : y = 40 := by 
    linarith [h6, hx]
  have hz : z = 80 := by 
    linarith [h10, hx]
  linarith [h₃, hx, hy, hz]