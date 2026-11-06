import Mathlib

theorem algebra_198573 (x : Fin 5 → ℕ) :
    x 0 + 11 * x 1 + 21 * x 2 + 31 * x 3 + 41 * x 4 = 55 ∧
    2 * x 0 + 12 * x 1 + 22 * x 2 + 32 * x 3 + 42 * x 4 = 60 ∧
    3 * x 0 + 13 * x 1 + 23 * x 2 + 33 * x 3 + 43 * x 4 = 65 ∧
    4 * x 0 + 14 * x 1 + 24 * x 2 + 34 * x 3 + 44 * x 4 = 70 ∧
    5 * x 0 + 15 * x 1 + 25 * x 2 + 35 * x 3 + 45 * x 4 = 75 ↔
    (x 0 = 0 ∧ x 1 = 5 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0) ∨
    (x 0 = 1 ∧ x 1 = 3 ∧ x 2 = 1 ∧ x 3 = 0 ∧ x 4 = 0) ∨
    (x 0 = 2 ∧ x 1 = 1 ∧ x 2 = 2 ∧ x 3 = 0 ∧ x 4 = 0) ∨
    (x 0 = 2 ∧ x 1 = 2 ∧ x 2 = 0 ∧ x 3 = 1 ∧ x 4 = 0) ∨
    (x 0 = 3 ∧ x 1 = 0 ∧ x 2 = 1 ∧ x 3 = 1 ∧ x 4 = 0) ∨
    (x 0 = 3 ∧ x 1 = 1 ∧ x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 1) := by
  constructor
  · -- Forward direction: equations imply the solutions
    rintro ⟨h1, h2, h3, h4, h5⟩
    have h6 : x 4 ≤ 1 := by omega
    have h7 : x 3 ≤ 1 := by omega
    have h8 : x 2 ≤ 2 := by omega
    have h9 : x 1 ≤ 5 := by omega
    have h10 : x 0 ≤ 5 := by omega
    interval_cases x 0 <;> 
      interval_cases x 1 <;> 
      interval_cases x 2 <;> 
      interval_cases x 3 <;> 
      interval_cases x 4 <;>
      simp at h1 h2 h3 h4 h5 ⊢ <;>
      omega
  · -- Backward direction: each of the solutions satisfies the equations
    rintro (h | h | h | h | h | h)
    · -- First solution
      rcases h with ⟨h0, h1, h2, h3, h4⟩
      constructor
      · -- First equation
        omega
      constructor
      · -- Second equation
        omega
      constructor
      · -- Third equation
        omega
      constructor
      · -- Fourth equation
        omega
      · -- Fifth equation
        omega
    · -- Second solution
      rcases h with ⟨h0, h1, h2, h3, h4⟩
      constructor
      · -- First equation
        omega
      constructor
      · -- Second equation
        omega
      constructor
      · -- Third equation
        omega
      constructor
      · -- Fourth equation
        omega
      · -- Fifth equation
        omega
    · -- Third solution
      rcases h with ⟨h0, h1, h2, h3, h4⟩
      constructor
      · -- First equation
        omega
      constructor
      · -- Second equation
        omega
      constructor
      · -- Third equation
        omega
      constructor
      · -- Fourth equation
        omega
      · -- Fifth equation
        omega
    · -- Fourth solution
      rcases h with ⟨h0, h1, h2, h3, h4⟩
      constructor
      · -- First equation
        omega
      constructor
      · -- Second equation
        omega
      constructor
      · -- Third equation
        omega
      constructor
      · -- Fourth equation
        omega
      · -- Fifth equation
        omega
    · -- Fifth solution
      rcases h with ⟨h0, h1, h2, h3, h4⟩
      constructor
      · -- First equation
        omega
      constructor
      · -- Second equation
        omega
      constructor
      · -- Third equation
        omega
      constructor
      · -- Fourth equation
        omega
      · -- Fifth equation
        omega
    · -- Sixth solution
      rcases h with ⟨h0, h1, h2, h3, h4⟩
      constructor
      · -- First equation
        omega
      constructor
      · -- Second equation
        omega
      constructor
      · -- Third equation
        omega
      constructor
      · -- Fourth equation
        omega
      · -- Fifth equation
        omega