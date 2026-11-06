import Mathlib

theorem algebra_219461 {x y : ℝ} (h₀ : x / y = 3) (h₁ : (x ^ 2 + y ^ 2) / (x + y) = 5) :
    x = 6 ∧ y = 2 := by
  have hy : y ≠ 0 := by
    by_contra h'
    rw [h'] at h₀
    norm_num at h₀
  have h2 : x + y ≠ 0 := by
    by_contra h'
    have h3 : x = -y := by linarith
    rw [h3] at h₁
    field_simp [show y ≠ 0 by exact hy] at h₁
    all_goals nlinarith
  have h2' : x = 3 * y := by
    have h3 : y ≠ 0 := hy
    field_simp [h3] at h₀
    linarith
  have h3 : x ^ 2 + y ^ 2 = 5 * (x + y) := by
    have h4 : x + y ≠ 0 := h2
    field_simp [h4] at h₁
    linarith
  rw [h2'] at h3
  have hy_val : y = 2 := by
    have h4 : y ^ 2 * 10 - 20 * y = 0 := by
      nlinarith
    have h5 : y * (y - 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h5) with hy1 hy2
    · -- y = 0 is impossible from hy: y ≠ 0
      contradiction
    · -- y - 2 = 0 => y = 2
      linarith
  have hx_val : x = 6 := by
    rw [hy_val] at h2'
    linarith
  exact ⟨hx_val, hy_val⟩