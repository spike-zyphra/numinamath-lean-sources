import Mathlib

open Real

theorem inequalities_142142 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / 2 ≥ sqrt (a * b) ∧ ((a + b) / 2 = sqrt (a * b) ↔ a = b) := by

  have h1 : (sqrt (a * b)) ^ 2 = a * b := by
    rw [Real.sq_sqrt]
    nlinarith [mul_nonneg ha hb]

  have h2 : (a + b) / 2 ≥ sqrt (a * b) := by
    have h3 : (sqrt (a * b)) ^ 2 = a * b := h1
    have h4 : ((a + b) / 2) ^ 2 ≥ a * b := by
      nlinarith [sq_nonneg (a - b)]
    have h5 : (sqrt (a * b)) ≥ 0 := Real.sqrt_nonneg (a * b)
    have h6 : ((a + b) / 2) ≥ 0 := by nlinarith
    nlinarith [Real.sqrt_nonneg (a * b), Real.sq_sqrt (show 0 ≤ a * b by nlinarith [ha, hb]), sq_nonneg (a - b), Real.sqrt_nonneg (a * b)]

  have h7 : (a + b) / 2 = sqrt (a * b) ↔ a = b := by
    constructor
    · -- Forward: (a + b)/2 = sqrt(a * b) → a = b
      intro h_eq
      have h_eq2 : (a + b) / 2 = sqrt (a * b) := h_eq
      have h10 : (sqrt (a * b)) ^ 2 = a * b := h1
      have h_eq3 : ((a + b) / 2) ^ 2 = (sqrt (a * b)) ^ 2 := by
        rw [h_eq2]
      have h_eq4 : ((a + b) / 2) ^ 2 = a * b := by 
        nlinarith [h_eq3, h1]
      have h_eq5 : (a - b) ^ 2 = 0 := by
        nlinarith
      have h_eq6 : a - b = 0 := by 
        apply pow_eq_zero 
        exact h_eq5
      linarith
    · -- Backward: a = b → (a + b)/2 = sqrt(a * b)
      intro h_eq
      rw [show b = a by linarith [h_eq]]
      have h11 : a * a = a ^ 2 := by
        nlinarith
      have h12 : sqrt (a * a) = sqrt (a ^ 2) := by
        rw [show a * a = a ^ 2 by nlinarith]
      have h13 : sqrt (a ^ 2) = a := Real.sqrt_sq (by linarith)
      have h14 : sqrt (a * a) = a := by
        rw [h12]
        exact h13
      nlinarith [Real.sqrt_nonneg (a * a), h14]

  constructor
  · exact h2
  · exact h7