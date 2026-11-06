import Mathlib

open Real

theorem inequalities_178256 (x y : Fin 3 → ℝ) (d : Fin 3 → ℝ)
    (h₀ : ∀ i, x i ≠ y i) (h₁ : ∀ i, d i = max (x i) (y i)) :
    (x 0 ≤ x 1 + x 2 ∧ y 0 ≤ y 1 + y 2) → d 0 ≤ d 1 + d 2 := by
  intro h
  rcases h with ⟨h2, h3⟩
  have h4 : d 0 = max (x 0) (y 0) := by
    specialize h₁ 0
    simpa using h₁
  have h5 : d 1 = max (x 1) (y 1) := by
    specialize h₁ 1
    simpa using h₁
  have h6 : d 2 = max (x 2) (y 2) := by
    specialize h₁ 2
    simpa using h₁
  rw [h4, h5, h6]
  by_cases h7 : x 0 ≤ y 0
  · -- Case 1: If x 0 ≤ y 0, then max (x 0) (y 0) = y 0
    have h8 : max (x 0) (y 0) = y 0 := by
      apply max_eq_right
      linarith
    rw [h8]
    have h9 : y 0 ≤ y 1 + y 2 := by linarith
    have h10 : max (x 1) (y 1) ≥ y 1 := by
      cases max_cases (x 1) (y 1) with
      | inl h => linarith
      | inr h => linarith
    have h11 : max (x 2) (y 2) ≥ y 2 := by
      cases max_cases (x 2) (y 2) with
      | inl h => linarith
      | inr h => linarith
    linarith
  · -- Case 2: If y 0 < x 0, then max (x 0) (y 0) = x 0
    have h8 : max (x 0) (y 0) = x 0 := by
      apply max_eq_left
      nlinarith
    rw [h8]
    have h12 : x 0 ≤ x 1 + x 2 := by linarith
    have h13 : max (x 1) (y 1) ≥ x 1 := by
      cases max_cases (x 1) (y 1) with
      | inl h => linarith
      | inr h => linarith
    have h14 : max (x 2) (y 2) ≥ x 2 := by
      cases max_cases (x 2) (y 2) with
      | inl h => linarith
      | inr h => linarith
    linarith