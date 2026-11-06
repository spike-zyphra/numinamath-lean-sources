import Mathlib
theorem algebra_1144 (x : ℝ)  :
    |1 - Real.sqrt ((x - 1)^2)| = x ↔ 0 ≤ x ∧ x ≤ 1 := by
  constructor
  · -- Forward direction: if |1 - sqrt((x - 1)^2)| = x, then 0 ≤ x ∧ x ≤ 1
    intro h_eq
    have h1 : 0 ≤ x := by
      cases abs_cases (1 - Real.sqrt ((x - 1) ^ 2)) with
      | inl h2 =>
        have h1 : Real.sqrt ((x - 1) ^ 2) ≥ 0 := Real.sqrt_nonneg ((x - 1) ^ 2)
        linarith
      | inr h2 =>
        have h1 : Real.sqrt ((x - 1) ^ 2) ≥ 0 := Real.sqrt_nonneg ((x - 1) ^ 2)
        linarith

    have h2 : Real.sqrt ((x - 1) ^ 2) = |x - 1| := by
      rw [Real.sqrt_sq_eq_abs]

    rw [h2] at h_eq

    have h4 : x ≤ 1 := by
      cases abs_cases (1 - |x - 1|) with
      | inl h5 =>
        cases abs_cases (x - 1) with
        | inl h6 =>
          nlinarith
        | inr h6 =>
          nlinarith
      | inr h5 =>
        cases abs_cases (x - 1) with
        | inl h6 =>
          nlinarith
        | inr h6 =>
          nlinarith

    constructor
    · exact h1
    · exact h4
  · -- Backward direction: if 0 ≤ x ∧ x ≤ 1, then |1 - Real.sqrt ((x - 1)^2)| = x
    rintro ⟨hx1, hx2⟩
    have h2 : Real.sqrt ((x - 1) ^ 2) = |x - 1| := by
      rw [Real.sqrt_sq_eq_abs]

    have h4 : |x - 1| = 1 - x := by
      have h5 : x - 1 ≤ (0 : ℝ) := by
        linarith
      rw [abs_of_nonpos h5]
      all_goals
        linarith

    have h5 : (1 - Real.sqrt ((x - 1)^2) : ℝ) = x := by
      rw [h2, h4]
      all_goals
        linarith

    rw [h5]
    rw [abs_of_nonneg (by linarith)]
    all_goals
      linarith