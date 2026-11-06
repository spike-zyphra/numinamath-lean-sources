import Mathlib

theorem algebra_260566 (x p : ℝ) (hx : x ≥ 0) (h : Real.sqrt (x + 3) + Real.sqrt x = p) :
    x = ((p ^ 2 - 3) ^ 2) / (4 * p ^ 2) := by
  have h1 : Real.sqrt (x + 3) = p - Real.sqrt x := by
    linarith
  have h2 : Real.sqrt (x + 3) ^ 2 = (p - Real.sqrt x) ^ 2 := by
    rw [h1]
  have h3 : Real.sqrt (x + 3) ^ 2 = x + 3 := by
    rw [Real.sq_sqrt]
    linarith
  have h4 : (p - Real.sqrt x) ^ 2 = p^2 - 2 * p * Real.sqrt x + (Real.sqrt x) ^ 2 := by
    ring
  have h5 : (Real.sqrt x) ^ 2 = x := by
    rw [Real.sq_sqrt]
    linarith
  rw [h3, h4, h5] at h2
  have h6 : 2 * p * Real.sqrt x = p^2 - 3 := by 
    nlinarith
  have hp : p ≠ 0 := by
    by_contra h0
    have h11 : Real.sqrt (x + 3) + Real.sqrt x = 0 := by
      rw [h0] at h
      linarith
    have h12 : Real.sqrt (x + 3) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h13 : Real.sqrt x ≥ 0 := by
      apply Real.sqrt_nonneg
    have h14 : Real.sqrt (x + 3) = 0 := by
      nlinarith
    have h15 : Real.sqrt x = 0 := by
      nlinarith
    have h16 : x = 0 := by
      have : Real.sqrt x = 0 := h15 
      rw [Real.sqrt_eq_zero (by linarith)] at this
      linarith
    have h17 : x + 3 = 0 := by
      have : Real.sqrt (x + 3) = 0 := h14 
      rw [Real.sqrt_eq_zero (by linarith)] at this
      linarith
    nlinarith
  have h7 : Real.sqrt x = (p^2 - 3) / (2 * p) := by
    field_simp [hp] at h6 ⊢ 
    nlinarith
  have h8 : Real.sqrt x ≥ 0 := by
    apply Real.sqrt_nonneg
  have h9 : (Real.sqrt x) ^ 2 = x := by
    rw [Real.sq_sqrt]
    linarith
  have h10 : x = ((p ^ 2 - 3) ^ 2) / (4 * p ^ 2) := by
    have eq1 : (Real.sqrt x) ^ 2 = x := h9
    rw [h7] at eq1
    field_simp at eq1 ⊢
    <;> ring_nf at eq1 ⊢
    <;> nlinarith [Real.sqrt_nonneg (x + 3), Real.sqrt_nonneg x, sq_nonneg (p), sq_nonneg (p - 3), sq_nonneg (Real.sqrt x - 0)]
  exact h10