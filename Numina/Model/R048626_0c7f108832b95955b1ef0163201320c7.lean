import Mathlib

theorem algebra_97529 {w x y z : ℝ} (h₀ : w / x = 4 / 3) (h₁ : y / z = 3 / 2)
    (h₂ : z / x = 1 / 6) : w / y = 16 / 3 := by
  have hx : x ≠ 0 := by
    by_contra h
    rw [h] at h₀
    norm_num at h₀
  have hz : z ≠ 0 := by
    by_contra h
    rw [h] at h₁
    norm_num at h₁
  have hw : w = 4 / 3 * x := by
    have h₃ : w / x = 4 / 3 := h₀
    field_simp [hx] at h₃
    linarith
  have hz_eq : z = 1 / 6 * x := by
    have h₄ : z / x = 1 / 6 := h₂
    field_simp [hx] at h₄
    linarith
  have hy : y = 3 / 2 * z := by
    have h₅ : y / z = 3 / 2 := h₁
    field_simp [hz] at h₅
    linarith
  have hy_eq_x : y = 1 / 4 * x := by
    rw [hy, hz_eq]
    ring
  have h : w / y = 16 / 3 := by
    rw [hw, hy_eq_x]
    have hx_ne : x ≠ 0 := hx
    field_simp [hx_ne]
    <;> linarith
  exact h