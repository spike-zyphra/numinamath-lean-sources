import Mathlib

theorem number_theory_7186 (s : Finset ℕ) (hs : s = {d : ℕ | ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ m ^ 3 + 2 * n ^ 2 = 801 ∧ d = Nat.gcd m n}) :
    ∑ d ∈ s, d = 4 := by
  have h2 : s = {1, 3} := by
    ext d
    simp only [Finset.mem_insert, Finset.mem_singleton]
    have h4 : d ∈ s ↔ (d = 1 ∨ d = 3) := by
      have h5 : d ∈ s ↔ d ∈ (s : Set ℕ) := by 
        simp [Finset.mem_coe]
      rw [h5]
      rw [show (s : Set ℕ) = {d : ℕ | ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ m ^ 3 + 2 * n ^ 2 = 801 ∧ d = Nat.gcd m n} by exact_mod_cast hs]
      constructor
      · -- First direction: if d ∈ s, then either d=1 or d=3.
        rintro h
        rcases h with ⟨m, n, hm, hn, heq, h_eq⟩
        have h1 : m ≤ 9 := by
          by_contra h
          push_neg at h
          have h2 : m ^ 3 ≥ 1000 := by
            have : m ≥ 10 := h
            have h11 : m ^ 3 ≥ 10 ^ 3 := by
              apply Nat.pow_le_pow_of_le_left; linarith
            linarith
          nlinarith
        have h2 : m ≤ 9 := h1
        interval_cases m <;> try { 
          norm_num at heq
          all_goals
          have : n ≤ 31 := by
            by_contra h
            push_neg at h
            have : 2 * n ^ 2 ≥ 2 * 32 ^ 2 := by
              nlinarith [h, sq_nonneg n]
            nlinarith
          interval_cases n <;> norm_num at heq <;> norm_num [h_eq] at *
          <;> omega 
        }
      · -- Backward: if either d=1 or d=3, then it's in s.
        rintro (rfl | rfl)
        · -- The case when d = 1.
          refine' ⟨1, 20, by norm_num, by norm_num, by norm_num, by norm_num [Nat.gcd]⟩
        · -- The case when d = 3.
          refine' ⟨9, 6, by norm_num, by norm_num, by norm_num, by norm_num [Nat.gcd]⟩
    tauto
  rw [h2]
  native_decide