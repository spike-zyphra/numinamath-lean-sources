import Mathlib

theorem algebra_294530 (a b : ℝ) : Real.sqrt (a^2 + b^2) = a + b ↔ a * b = 0 ∧ a + b ≥ 0 := by
  constructor
  · -- Assume √(a² + b²) = a + b, prove a * b = 0 ∧ a + b ≥ 0
    intro h
    have h1 : a + b ≥ 0 := by
      have h2 : Real.sqrt (a^2 + b^2) ≥ 0 := Real.sqrt_nonneg (a^2 + b^2)
      linarith [h, h2]
    have h3 : a^2 + b^2 = (a + b)^2 := by
      calc
        a^2 + b^2 = (Real.sqrt (a^2 + b^2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = (a + b) ^ 2 := by rw [h]
    have h4 : a * b = 0 := by
      nlinarith
    exact ⟨h4, h1⟩
  · -- Assume a * b = 0 ∧ a + b ≥ 0, prove √(a² + b²) = a + b
    rintro ⟨h1, h2⟩
    have h3 : a^2 + b^2 = (a + b)^2 := by
      nlinarith
    have h4 : Real.sqrt (a^2 + b^2) = Real.sqrt ((a + b) ^ 2) := by
      rw [h3]
    have h5 : Real.sqrt ((a + b) ^ 2) = a + b := by
      rw [Real.sqrt_sq]
      linarith
    rw [h4, h5]