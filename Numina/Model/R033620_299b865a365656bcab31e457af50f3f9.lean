import Mathlib

theorem algebra_273704 {k1 k2 : ℝ} (h : k1 ≠ k2) (h1 : ∃! x : ℝ, x^2 + 2 * k1 * x + 7 * k1 - 10 = 0)
    (h2 : ∃! x : ℝ, x^2 + 2 * k2 * x + 7 * k2 - 10 = 0) :
    k1 + k2 = 7 := by

  rcases h1 with ⟨x1, hx1, h1_eq⟩
  rcases h2 with ⟨x2, hx2, h2_eq⟩

  have h11 : x1^2 + 2 * k1 * x1 + 7 * k1 - 10 = 0 := hx1
  have h12 : ∀ (y : ℝ), y^2 + 2 * k1 * y + 7 * k1 - 10 = 0 → y = x1 := h1_eq

  have h_eq1 : x1 = -k1 := by
    have h12' := h12 (-2 * k1 - x1) (by
      nlinarith [h11]
    )
    nlinarith

  have h_eq3 : k1^2 - 7 * k1 + 10 = 0 := by
    have h_x1 : x1 = -k1 := h_eq1
    rw [h_x1] at h11
    nlinarith

  have h21 : x2^2 + 2 * k2 * x2 + 7 * k2 - 10 = 0 := hx2
  have h22 : ∀ (z : ℝ), z^2 + 2 * k2 * z + 7 * k2 - 10 = 0 → z = x2 := h2_eq

  have h_eq2 : x2 = -k2 := by
    have h22' := h22 (-2 * k2 - x2) (by
      nlinarith [h21]
    )
    nlinarith

  have h_eq4 : k2^2 - 7 * k2 + 10 = 0 := by
    have h_x2 : x2 = -k2 := h_eq2
    rw [h_x2] at h21
    nlinarith
  
  have h_eq5 : k1^2 - 7 * k1 + 10 = 0 := h_eq3
  have h_eq6 : k2^2 - 7 * k2 + 10 = 0 := h_eq4
  
  have h_eq7 : (k1 - k2) * (k1 + k2 - 7) = 0 := by
    nlinarith

  cases' (mul_eq_zero.1 h_eq7) with h_eq8 h_eq9
  · -- Case 1: k1 - k2 = 0
    exfalso
    apply h
    linarith
  · -- Case 2: k1 + k2 - 7 = 0
    linarith