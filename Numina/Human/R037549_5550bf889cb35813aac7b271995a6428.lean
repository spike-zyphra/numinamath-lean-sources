import Mathlib


/- What is the minimum number of different prime numbers that must be randomly selected to ensure that
there are two numbers whose difference is divisible by $6$? -/
theorem number_theory_634252 : IsLeast
  {n : ℕ | ∀ s : Finset ℕ, s.card = n → (∀p ∈ s, p.Prime) →
  ∃ p ∈ s, p.Prime ∧ ∃ q ∈ s, q.Prime ∧ p ≠ q ∧ (6:ℤ) ∣ p - q} 5 := by

  rw [IsLeast, lowerBounds]
  simp only [Set.mem_setOf_eq]
  constructor

  · intro s hs hp
    -- prime number mod 6 can only be 1,2,3,5
    have h1: ∀p ∈ s, p % 6 ∈ ({1,2,3,5}: Finset ℕ) := by
      intro p p_in
      specialize hp p p_in
      mod_cases h: p % 6
      · have: 6 ∣ p := by
          exact Nat.dvd_of_mod_eq_zero h
        rw [hp.dvd_iff_eq (by norm_num)] at this
        norm_num [this] at hp
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        left; exact h
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        right; left; exact h
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        right; right; left; exact h
      · symm at h
        rw [Nat.modEq_iff_dvd] at h
        norm_num at h
        have: 2 ∣ p := by
          zify
          have h1: 2 ∣ (p-4:ℤ) := by
            apply Int.dvd_trans ?_ h
            norm_num
          have h2: 2 ∣ (4:ℤ) := by norm_num
          exact (Int.dvd_iff_dvd_of_dvd_sub h1).mpr h2
        rw [hp.dvd_iff_eq (by norm_num)] at this
        norm_num [this]
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        right; right; right; exact h

    -- since we choose 5 primes, at least two of them mod 6 equal.
    have h2: ({1,2,3,5}: Finset ℕ).card < s.card := by
      norm_num [hs]
    replace h2 := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      h2 h1
    rcases h2 with ⟨q1, hq1, q2, hq2, qne, qmod⟩
    use q1
    refine ⟨hq1, hp q1 hq1, q2, hq2, hp q2 hq2, qne, ?_⟩
    have: (6:ℤ) = ↑(6:ℕ) := by norm_num
    rw [this, ← Nat.modEq_iff_dvd]
    symm; exact qmod


  · intro n h
    -- {2, 3, 5, 7} witness n < 5 leads to contradiction
    by_contra!
    replace: n ≤ 4 := by exact Nat.le_of_lt_succ this
    
    -- in this lean version, aesop can't close the goal if we do not provide following lemmas.
    have h61: ¬ (6:ℤ) ∣ 1 := by norm_num
    have h62: ¬ (6:ℤ) ∣ 2 := by norm_num
    have h63: ¬ (6:ℤ) ∣ 3 := by norm_num
    have h64: ¬ (6:ℤ) ∣ 4 := by norm_num
    have h65: ¬ (6:ℤ) ∣ 5 := by norm_num

    interval_cases n
    · specialize h ∅ (by simp) (by simp)
      rcases h with ⟨p, hp⟩
      simp at hp
    · specialize h {2} (by simp) (by norm_num)
      rcases h with ⟨p, hp, _, q, hq, _, pneq, _⟩
      simp only [Finset.mem_singleton] at hp hq
      simp [hp,hq] at pneq
    · specialize h {2,3} (by norm_num) (by norm_num)
      aesop
    · specialize h {2,3,5} (by norm_num) (by norm_num)
      aesop
    · specialize h {2,3,5,7} (by norm_num) (by norm_num)
      aesop