import Mathlib

theorem algebra_10292 : {A : ℕ | A > 0 ∧ A < 10 ∧ ∀ x : ℂ, x^2 - (10 + A) * x + 10 * A = 0 → ∃ n : ℕ, n > 0 ∧ x = n}.encard = 9 := by

  have h1 : {A : ℕ | A > 0 ∧ A < 10 ∧ ∀ x : ℂ, x^2 - (10 + A) * x + 10 * A = 0 → ∃ n : ℕ, n > 0 ∧ x = n} = Set.Icc 1 9 := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- First, suppose A ∈ left side, need to prove A ∈ right side, which means 1 ≤ A ≤ 9.
      rintro ⟨hA1, hA2, h⟩
      have h2 : 1 ≤ A := by omega
      have h3 : A ≤ 9 := by omega
      exact ⟨h2, h3⟩
    · -- Suppose A ∈ right side, i.e., 1 ≤ A ≤ 9
      rintro ⟨h2, h3⟩
      constructor
      · -- Show A > 0
        omega
      constructor
      · -- Show A < 10
        omega
      · -- Show ∀ x : ℂ, x^2 - (10 + A) * x + 10 * A = 0 → ∃ n : ℕ, n > 0 ∧ x = n
        intro x hx
        have eq : x ^ 2 - (10 + A) * x + 10 * A = 0 := by
          simpa using hx
        have h4 : (x - 10) * (x - (A : ℂ)) = 0 := by
          have h5 : x ^ 2 - (10 + (A : ℂ)) * x + 10 * (A : ℂ) = 0 := by
            simpa using hx
          have eq1 : x ^ 2 - (10 + (A : ℂ)) * x + 10 * (A : ℂ) = (x - 10) * (x - (A : ℂ)) := by
            ring_nf
          rw [eq1] at h5
          simpa using h5
        cases (mul_eq_zero.1 h4) with
        | inl h10 =>
          have eq10 : x = (10 : ℂ) := by 
            have h4 : x - (10 : ℂ) = 0 := by exact_mod_cast h10
            have h5 : x = (10 : ℂ) := by 
              calc
                x = (x - (10 : ℂ)) + (10 : ℂ) := by ring_nf
                _ = (0 : ℂ) + (10 : ℂ) := by rw [h4]
                _ = (10 : ℂ) := by ring_nf
            exact_mod_cast h5
          exact ⟨10, by norm_num, by exact_mod_cast eq10⟩
        | inr hA =>
          have eqA : x = (A : ℂ) := by
            have h4 : x - (A : ℂ) = 0 := by exact_mod_cast hA
            have h5 : x = (A : ℂ) := by 
              calc
                x = (x - (A : ℂ)) + (A : ℂ) := by ring_nf
                _ = (0 : ℂ) + (A : ℂ) := by rw [h4]
                _ = (A : ℂ) := by ring_nf
            exact_mod_cast h5
          exact ⟨A, by omega, by exact_mod_cast eqA⟩
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_eq_toFinset_card']