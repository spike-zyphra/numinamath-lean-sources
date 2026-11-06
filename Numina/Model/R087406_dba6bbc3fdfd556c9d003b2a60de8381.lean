import Mathlib

theorem algebra_2687 {x : ℝ} (hx : x ≠ 0 ∧ x ≠ 1) (h : (x - 1) / (1 - (x - 1) / x) = -1 / 4) :
    x = 1 / 2 := by
  have h1 : x ≠ 0 := hx.1
  have h2 : x ≠ 1 := hx.2

  have hsimp : (x - 1) / (1 - (x - 1) / x) = x ^ 2 - x := by
    have h3 : x ≠ 0 := h1
    have h4 : x - 1 ≠ 0 := by intro h5; apply h2; linarith
    field_simp [h3, h4]
    <;> ring

  rw [hsimp] at h

  have h_eq : (x - 1/2)^2 = 0 := by
    nlinarith
  
  have h_zero : x - 1/2 = 0 := by
    rw [sq_eq_zero_iff] at h_eq 
    exact h_eq
  
  linarith