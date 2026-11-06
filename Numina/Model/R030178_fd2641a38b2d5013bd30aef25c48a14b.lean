import Mathlib

theorem algebra_206371 (m n : ℤ) : n^2 - 6 * n = m^2 + m - 10 ↔ (m, n) = (1, 4) ∨ (m, n) = (1, 2) ∨ (m, n) = (-2, 2) ∨ (m, n) = (-2, 4) := by
  constructor
  · -- Forward direction: if $n^2 - 6n = m^2 + m -10$, then $(m, n)$ is one of the four pairs.
    rintro h
    have h1 : 4 * (n - 3) ^ 2 - (2 * m + 1) ^ 2 = -5 := by
      nlinarith [h]
    have h2 : (2 * (n - 3) - (2 * m + 1)) * (2 * (n - 3) + (2 * m + 1)) = -5 := by
      nlinarith [h1]
    have h3 : (2 * (n - 3) - (2 * m + 1)) * (2 * (n - 3) + (2 * m + 1)) = -5 := h2
    have h4 : (2 * (n - 3) - (2 * m + 1)) ∣ -5 := by
      use (2 * (n - 3) + (2 * m + 1))
      all_goals linarith
    have h5 : (2 * (n - 3) - (2 * m + 1)) ∣ (5 : ℤ) := by
      exact Int.dvd_neg.mp h4
    have : (2 * (n - 3) - (2 * m + 1)) ≤ 5 := by
      exact Int.le_of_dvd (by decide) h5
    have : (2 * (n - 3) - (2 * m + 1)) ≥ -5 := by
      have h6 : (- (2 * (n - 3) - (2 * m + 1))) ∣ (5 : ℤ) := by
        exact Int.neg_dvd.2 h5
      have h7 : - (2 * (n - 3) - (2 * m + 1)) ≤ 5 := by
        exact Int.le_of_dvd (by decide) h6
      omega
    interval_cases h6 : (2 * (n - 3) - (2 * m + 1)) <;> norm_num at h2
    <;> try { 
      omega 
    }
    <;> try { 
      norm_num [Prod.ext_iff] at *
      <;> omega 
    }
  · -- Backward direction: if $(m, n)$ is one of the four pairs, then $n^2 - 6 n = m^2 + m - 10$.
    rintro (h | h | h | h)
    · -- Case $(1, 4)$
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Case $(1, 2)$
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Case $(-2, 2)$
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Case $(-2, 4)$
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num