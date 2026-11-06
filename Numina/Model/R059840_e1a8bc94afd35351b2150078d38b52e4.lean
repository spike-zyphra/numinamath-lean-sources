import Mathlib

theorem algebra_6025 (x : Fin 3 → ℤ) (hx : ∀ i, 0 ≤ x i) :
    15 * x 0 + 10 * x 1 + 6 * x 2 = 61 ↔
    (x 0 = 1 ∧ x 1 = 1 ∧ x 2 = 6) ∨
    (x 0 = 3 ∧ x 1 = 1 ∧ x 2 = 1) ∨
    (x 0 = 1 ∧ x 1 = 4 ∧ x 2 = 1) := by
  constructor
  · -- Assume the equation 15 * x 0 + 10 * x 1 + 6 * x 2 = 61 and prove the opposite.
    rintro h
    have hx0 : 0 ≤ x 0 := hx 0
    have hx1 : 0 ≤ x 1 := hx 1
    have hx2 : 0 ≤ x 2 := hx 2

    have h1 : x 0 ≤ 4 := by
      omega

    have h2 : x 1 ≤ 6 := by
      omega

    have h3 : x 2 ≤ 10 := by
      omega

    interval_cases h4 : x 0 <;> 
      interval_cases h5 : x 1 <;> 
        omega

  · -- Assume the reverse of the goal and prove the equation.
    rintro (h | h | h)
    · -- Case 1.
      rcases h with ⟨h1, h2, h3⟩
      linarith
    · -- Case 2.
      rcases h with ⟨h1, h2, h3⟩
      linarith
    · -- Case 3.
      rcases h with ⟨h1, h2, h3⟩
      linarith