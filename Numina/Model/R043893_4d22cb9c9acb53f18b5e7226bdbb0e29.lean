import Mathlib

theorem algebra_299715 {p q : ℝ} (f : ℝ → ℝ) (hf : f = fun x => x^2 + p * x + q)
    (M : ℝ × ℝ) (hM : M.1^2 + p * M.1 + q < 0) :
    (∃ x1 x2 : ℝ, x1 ≠ x2 ∧ f x1 = 0 ∧ f x2 = 0 ∧ x1 < x2 ∧ x1 < M.1 ∧ M.1 < x2) := by
  have h1 : p^2 - 4*q > 0 := by
    nlinarith [sq_nonneg (M.1 + p/2), sq_nonneg (p + 2 * M.1), sq_nonneg (M.1), sq_nonneg (M.1 + p)]
  use (-p - Real.sqrt (p^2 - 4*q)) / 2, (-p + Real.sqrt (p^2 - 4*q)) / 2 
  constructor 
  · -- Show x1 ≠ x2
    by_contra h
    have h3 : Real.sqrt (p^2 - 4*q) = 0 := by
      nlinarith 
    have h4 : Real.sqrt (p^2 - 4*q) ≥ 0 := Real.sqrt_nonneg (p^2 - 4*q)
    have h5 : Real.sqrt (p^2 - 4*q) > 0 := by
      have h6 : p^2 - 4*q > 0 := h1
      have : Real.sqrt (p^2 - 4*q) > 0 := by
        apply Real.sqrt_pos.mpr
        linarith 
      linarith 
    linarith 
  constructor 
  · -- Show f x1 = 0 
    rw [hf]
    have h6 : ((-p - Real.sqrt (p^2 - 4*q)) / 2)^2 + p * ((-p - Real.sqrt (p^2 - 4*q)) / 2) + q = 0 := by
      nlinarith [Real.sqrt_nonneg (p^2 - 4*q), Real.sq_sqrt (show (0 : ℝ) ≤ p^2 - 4*q by linarith)]
    simpa using h6 
  constructor 
  · -- Show f x2 = 0 
    rw [hf]
    have h7 : ((-p + Real.sqrt (p^2 - 4*q)) / 2)^2 + p * ((-p + Real.sqrt (p^2 - 4*q)) / 2) + q = 0 := by
      nlinarith [Real.sqrt_nonneg (p^2 - 4*q), Real.sq_sqrt (show (0 : ℝ) ≤ p^2 - 4*q by linarith)]
    simpa using h7 
  constructor 
  · -- Show x1 < x2 
    have h5 : Real.sqrt (p^2 - 4*q) > 0 := by 
      have h6 : p^2 - 4*q > 0 := h1 
      have : Real.sqrt (p^2 - 4*q) > 0 := by 
        apply Real.sqrt_pos.mpr 
        linarith 
      linarith 
    nlinarith [Real.sqrt_nonneg (p^2 - 4*q)]
  constructor 
  · -- Show x1 < M.1 
    have h5 : Real.sqrt (p^2 - 4*q) > 0 := by
      have h6 : p^2 - 4*q > 0 := h1
      have : Real.sqrt (p^2 - 4*q) > 0 := by
        apply Real.sqrt_pos.mpr 
        linarith 
      linarith 
    nlinarith [Real.sqrt_nonneg (p^2 - 4*q), Real.sq_sqrt (show (0 : ℝ) ≤ p^2 - 4*q by linarith), sq_nonneg (M.1 + p/2)]
  · -- Show M.1 < x2 
    have h5 : Real.sqrt (p^2 - 4*q) > 0 := by
      have h6 : p^2 - 4*q > 0 := h1 
      have : Real.sqrt (p^2 - 4*q) > 0 := by 
        apply Real.sqrt_pos.mpr 
        linarith 
      linarith 
    nlinarith [Real.sqrt_nonneg (p^2 - 4*q), Real.sq_sqrt (show (0 : ℝ) ≤ p^2 - 4*q by linarith), sq_nonneg (M.1 + p/2)]