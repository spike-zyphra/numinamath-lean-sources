import Mathlib

theorem algebra_316749 {n : ℕ} (hn : n > 0) :
    ∃ f : Fin n → Polynomial ℚ, ∀ x : ℚ, x^2 + 7 = ∑ i : Fin n, (f i).eval x ^ 2 ↔ n = 5 := by
  by_cases h : n = 5
  · -- n = 5
    rw [h]
    use λ i =>
      match i with
      | 0 => Polynomial.X
      | 1 => Polynomial.C (2 : ℚ)
      | 2 => Polynomial.C (1 : ℚ)
      | 3 => Polynomial.C (1 : ℚ)
      | 4 => Polynomial.C (1 : ℚ)
      | _ => Polynomial.C (0 : ℚ)
    intro x
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    all_goals
      ring_nf
  · -- n ≠ 5
    have hn' : n ≠ 5 := by
      intro hn1
      apply h
      omega
    use λ _ => (Polynomial.C (0 : ℚ) : Polynomial ℚ)
    intro x
    constructor
    · -- Assume x^2 + 7 = 0, prove n = 5
      intro h_eq
      have h0 : x ^ 2 + 7 = (0 : ℚ) := by
        simpa using h_eq
      have h1 : x ^ 2 ≥ 0 := sq_nonneg x
      have h2 : (7 : ℚ) ≤ x ^ 2 := by linarith
      nlinarith
    · -- Assume n = 5, prove x^2 + 7 = 0
      intro h_eq
      exfalso
      apply hn'
      omega