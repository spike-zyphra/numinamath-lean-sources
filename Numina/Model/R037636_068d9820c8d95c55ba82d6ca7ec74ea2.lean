import Mathlib

theorem number_theory_606216 (a : ℕ → ℚ)
    (h₀ : a 1 = 9)
    (h₁ : ∀ n ≥ 1, a (n + 1) = ((n + 5) * a n + 22) / (n + 3)) :
    {n | 1 ≤ n ∧ ∃ m : ℕ, m^2 = (a n) } = {1, 8} := by

  have h2 : ∀ n, 0 < n → a n = ((n : ℚ) ^ 2 + 7 * (n : ℚ) + 1) := by
    intro n hn
    induction n with
    | zero =>
      exfalso
      linarith
    | succ n ih =>
      by_cases h : n = 0
      · rw [h]
        norm_num [h₀]
      · have h5 : n ≥ 1 := by
          omega
        have h7 : a (n + 1) = ((n + 1 : ℚ) ^ 2 + 7 * (n + 1 : ℚ) + 1) := by
          have h8 : a (n + 1) = ((n + 5) * a n + 22) / (n + 3) := h₁ n (by omega)
          rw [h8]
          have h9 : a n = ((n : ℚ) ^ 2 + 7 * (n : ℚ) + 1) := ih (by omega)
          rw [h9]
          field_simp
          ring_nf
        simpa using h7

  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- First prove {n | 1 ≤ n ∧ ∃ m : ℕ, m ^ 2 = a n} ⊆ {1, 8}
    intro h
    rcases h with ⟨hn1, m, hm⟩
    have h3 : a n = ((n : ℚ) ^ 2 + 7 * (n : ℚ) + 1) := h2 n (by omega)
    have h4 : (m : ℚ) ^ 2 = ((n : ℚ) ^ 2 + 7 * (n : ℚ) + 1) := by
      rw [← h3]
      exact_mod_cast hm

    have h5 : 4 * (m : ℤ) ^ 2 = (2 * (n : ℤ) + 7) ^ 2 - 45 := by
      have h6 : (4 : ℚ) * (m : ℚ) ^ 2 = (2 * (n : ℚ) + 7) ^ 2 - 45 := by
        have h7 : (m : ℚ) ^ 2 = (n : ℚ) ^ 2 + 7 * (n : ℚ) + 1 := by linarith
        nlinarith
      exact_mod_cast h6

    have h8 : (2 * (n : ℤ) + 7 - 2 * (m : ℤ)) * (2 * (n : ℤ) + 7 + 2 * (m : ℤ)) = 45 := by
      nlinarith

    have h9 : (2 * (n : ℤ) + 7 - 2 * (m : ℤ)) ∣ 45 := by
      use (2 * (n : ℤ) + 7 + 2 * (m : ℤ))
      all_goals linarith

    have h10 : (2 * (n : ℤ) + 7 - 2 * (m : ℤ)) ≤ 45 := by
      apply Int.le_of_dvd (show 0 < 45 by norm_num) h9
    have h11 : (2 * (n : ℤ) + 7 - 2 * (m : ℤ)) ≥ -45 := by
      have h11 : - (2 * (n : ℤ) + 7 - 2 * (m : ℤ)) ∣ 45 := by
        exact Int.neg_dvd.2 h9
      have h12 : - (2 * (n : ℤ) + 7 - 2 * (m : ℤ)) ≤ 45 := by
        apply Int.le_of_dvd (show 0 < 45 by norm_num) h11
      omega

    have hn8 : n = 1 ∨ n = 8 := by
      have h7 : (n : ℤ) = 1 ∨ (n : ℤ) = 8 := by
        interval_cases h13 : (2 * (n : ℤ) + 7 - 2 * (m : ℤ)) <;> omega
      omega

    tauto

  · -- Now prove {1, 8} ⊆ {n | 1 ≤ n ∧ ∃ m : ℕ, m ^ 2 = a n}
    rintro (rfl | rfl)
    · constructor
      · norm_num
      · use 3
        norm_num [h2 1 (by norm_num)]
    · constructor
      · norm_num
      · use 11
        norm_num [h2 8 (by norm_num)]