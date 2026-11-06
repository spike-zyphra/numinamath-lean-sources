import Mathlib

theorem number_theory_129138 (n : ℕ) : (n^2 + 11) ∣ (n^3 + 13) ↔ n = 3 ∨ n = 8 := by
  constructor
  · -- Forward direction: if (n^2 + 11) divides (n^3 + 13), then n = 3 or n = 8
    intro h
    by_cases h1 : n ≤ 8
    · -- When n ≤ 8, check all possible values
      interval_cases n <;> norm_num at h ⊢ <;> omega
    · -- Case n > 8
      have h2 : n > 8 := by omega
      have h3 : n ≥ 9 := by omega
      have h4 : ((n : ℤ) ^ 2 + 11) ∣ ((n : ℤ) ^ 3 + 13) := by
        have h5 : (n ^ 2 + 11) ∣ (n ^ 3 + 13) := h
        have h11 : ((n ^ 2 + 11 : ℤ) ) ∣ ((n ^ 3 + 13 : ℤ)) := by
          have h5' : (n ^ 2 + 11) ∣ (n ^ 3 + 13) := h
          have h12 : ((n ^ 2 + 11 : ℤ) ) ∣ ((n ^ 3 + 13 : ℤ)) := by
            exact_mod_cast h5'
          exact_mod_cast h12
        exact_mod_cast h11
      have h5 : ((n : ℤ) ^ 2 + 11) ∣ (11 * (n : ℤ) - 13) := by
        have h6 : ((n : ℤ) ^ 2 + 11) ∣ (( (n : ℤ) ^ 3 + 13 ) - ( (n : ℤ) * ( (n : ℤ) ^ 2 + 11 ) ) ) := by
          apply Dvd.dvd.sub
          · -- Show that ((n : ℤ) ^ 2 + 11) ∣ (( (n : ℤ) ^ 3 + 13 ))
            exact h4
          · -- Show that ((n : ℤ) ^ 2 + 11) ∣ ( (n : ℤ) * ( (n : ℤ) ^ 2 + 11 ) )
            apply dvd_mul_of_dvd_right
            exact dvd_refl ((n : ℤ) ^ 2 + 11)
        have h7 : ( ( (n : ℤ) ^ 3 + 13 ) - ( (n : ℤ) * ( (n : ℤ) ^ 2 + 11 ) ) ) = (13 - 11 * (n : ℤ) ) := by
          ring_nf
          <;> omega
        rw [h7] at h6
        have h8 : ((n : ℤ) ^ 2 + 11) ∣ (11 * (n : ℤ) - 13) := by
          have h9 : ((n : ℤ) ^ 2 + 11) ∣ (13 - 11 * (n : ℤ) ) := h6
          have h10 : ((n : ℤ) ^ 2 + 11) ∣ -( (13 - 11 * (n : ℤ) ) ) := by
            exact Dvd.dvd.neg_right h9
          have h11 : -( (13 - 11 * (n : ℤ) ) ) = (11 * (n : ℤ) - 13) := by
            ring_nf
          rw [h11] at h10
          exact_mod_cast h10
        exact_mod_cast h8

      have h6 : (n : ℤ) ^ 2 + 11 ≤ 11 * (n : ℤ) - 13 := by
        have h7 : ((n : ℤ) ^ 2 + 11) ∣ (11 * (n : ℤ) - 13) := h5
        have h8 : (11 * (n : ℤ) - 13) > 0 := by
          have hn1 : (n : ℤ) ≥ 9 := by
            omega
          omega
        by_contra h
        push_neg at h
        have h10 : ( (n : ℤ) ^ 2 + 11 ) > ( 11 * (n : ℤ) - 13 ) := by linarith
        have h11 : ( (n : ℤ) ^ 2 + 11 ) ∣ ( 11 * (n : ℤ) - 13 ) := h7
        have h12 : ( (n : ℤ) ^ 2 + 11 ) ≤ ( 11 * (n : ℤ) - 13 ) := by
          apply Int.le_of_dvd ( by omega ) h11
        nlinarith

      have h7 : (n : ℤ) ≤ 8 := by
        nlinarith [h6, sq_nonneg ((n : ℤ) - 3 : ℤ), sq_nonneg ((n : ℤ) - 8 : ℤ)]
      omega
  · -- Backward direction: if n = 3 or n = 8, then (n^2 + 11) divides (n^3 + 13)
    rintro (rfl | rfl)
    · -- For n = 3, check the divisibility
      norm_num
    · -- For n = 8, check the divisibility
      norm_num