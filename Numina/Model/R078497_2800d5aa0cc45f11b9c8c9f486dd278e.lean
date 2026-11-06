import Mathlib

theorem algebra_136540 {x : ℝ} (hx : x ≠ 0) (h : x + 1/x = Real.sqrt 5) :
    x^11 - 7*x^7 + x^3 = 0 := by
  have h1 : x^2 + 1 = x * Real.sqrt 5 := by
    have h2 : x ≠ 0 := hx
    field_simp at h ⊢
    nlinarith
  have h2 : (x^2 + 1) ^ 2 = (x * Real.sqrt 5)^2 := by
    rw [h1]
  have h3 : (x^2 + 1) ^ 2 = x^4 + 2*x^2 + 1 := by ring
  have h4 : (x * Real.sqrt 5)^2 = x^2 * 5 := by
    calc
      (x * Real.sqrt 5)^2 = x^2 * (Real.sqrt 5)^2 := by ring
      _ = x^2 * 5 := by rw [Real.sq_sqrt]; linarith [Real.sqrt_nonneg 5]
  rw [h3, h4] at h2
  have h5 : x^4 - 3*x^2 + 1 = 0 := by
    nlinarith
  have h8 : x^8 - 7*x^4 + 1 = 0 := by
    have h7 : x^4 = 3 * x^2 - 1 := by linarith
    have h9 : x^8 = (x^4)^2 := by ring
    rw [h9, h7]
    nlinarith [h5]
  have h11 : x^11 - 7*x^7 + x^3 = x^3 * (x^8 - 7*x^4 + 1) := by ring
  rw [h11, h8]
  <;> ring