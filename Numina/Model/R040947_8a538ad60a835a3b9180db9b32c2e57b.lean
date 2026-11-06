import Mathlib

theorem algebra_93610 (x y: ℝ) (hy : y ≠ 0) : 
(∃ k : ℝ , x + y = 0 → (y = k * x ∨ x * y = k)) ∧
(∃ k : ℝ , 3*x*y = 10 → (y = k * x ∨ x * y = k)) ∧ 
(∃ k : ℝ , x = 5*y → (y = k * x ∨ x * y = k)) ∧ 
(∃ k : ℝ , x/y = √3 → (y = k * x ∨ x * y = k)) := by
  constructor
  · -- Equation (A) x + y = 0: We can write y = -x, which is direct proportionality.
    use -1
    intro h
    left
    linarith
  constructor
  · -- Equation (B) 3xy = 10: This is inverse proportionality with k = 10/3.
    use 10 / 3
    intro h
    right
    nlinarith
  constructor
  · -- Equation (C) x = 5y: We can write y = 1/5 * x, which is direct proportionality.
    use 1 / 5
    intro h
    left
    linarith
  · -- Equation (E) x / y = sqrt 3: This is direct proportionality.
    use 1 / Real.sqrt 3
    intro h
    left
    have h1 : x = y * Real.sqrt 3 := by
      field_simp [hy] at h ⊢
      <;> nlinarith
    have h2 : y = (1 / Real.sqrt 3) * x := by
      have h3 : Real.sqrt 3 ≠ 0 := by
        positivity
      have h4 : y = x / Real.sqrt 3 := by
        field_simp [h3] at h1 ⊢
        linarith
      rw [h4]
      field_simp
    linarith