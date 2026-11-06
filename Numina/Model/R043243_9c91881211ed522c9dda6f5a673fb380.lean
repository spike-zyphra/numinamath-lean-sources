import Mathlib

open Finset

theorem number_theory_102360 {A B : Set ℕ} (A : ℕ → ℕ)
    (hA : ∀ n > 0, A n = Nat.factorial n + 57)
    (hB : B = {y ^ 4 | y : ℕ}) :
    A 9 ∉ B ∧ {x : ℕ | ∃ n > 0, x = A n} ∩ B = {81} := by
  have h1 : A 9 ∉ B := by 
    rw [hA 9 (by norm_num)]
    rw [hB]
    intro h 
    rcases h with ⟨y, hy⟩
    norm_num [Nat.factorial] at hy
    have h2 : y ≤ 25 := by
      by_contra h
      push_neg at h
      have h3 : y ^ 4 ≥ 26 ^ 4 := by
        have h4 : y ≥ 26 := by linarith
        have h5 : y ^ 4 ≥ 26 ^ 4 := by
          apply Nat.pow_le_pow_of_le_left
          linarith
        linarith
      nlinarith
    interval_cases y <;> norm_num at hy
    all_goals
      omega
  have h2 : {x : ℕ | ∃ n > 0, x = A n} ∩ B = {81} := by
    ext x
    simp only [Set.mem_inter, Set.mem_setOf_eq, Set.mem_singleton_iff, hB]
    constructor
    · -- Assume $x \in A \cap B$, prove $x = 81$
      rintro ⟨⟨n, hn, hxn⟩, ⟨y, hy⟩⟩
      rw [hA n hn] at hxn
      by_cases h : n ≤ 4
      · -- Assume n <= 4
        interval_cases n <;> try { 
          simp [Nat.factorial] at hxn
          all_goals
            have h3 : y ≤ 10 := by
              by_contra h4
              push_neg at h4
              have h5 : y ^ 4 ≥ 11 ^ 4 := by
                have h6 : y ≥ 11 := by linarith
                have h7 : y ^ 4 ≥ 11 ^ 4 := by
                  apply Nat.pow_le_pow_of_le_left
                  linarith
                linarith
              nlinarith
            interval_cases y <;> norm_num at hxn hy ⊢
            <;> omega
          }
      · -- Assume n > 4
        have h4 : n ≥ 5 := by 
          omega 
        have h6 : (Nat.factorial n + 57) % 5 = 2 := by 
          have h10 : n ≥ 5 := h4
          have h11 : 5 ∣ Nat.factorial n := by 
            apply Nat.dvd_factorial
            all_goals 
              omega 
          have h12 : Nat.factorial n % 5 = 0 := by
            omega 
          omega 
        have h5 : y ^ 4 % 5 = 0 ∨ y ^ 4 % 5 = 1 := by 
          have h10 : y % 5 = 0 ∨ y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by 
            omega 
          rcases h10 with (h | h | h | h | h)
          · 
            simp [Nat.pow_mod, h]
          · 
            simp [Nat.pow_mod, h]
          · 
            simp [Nat.pow_mod, h]
          · 
            simp [Nat.pow_mod, h]
          · 
            simp [Nat.pow_mod, h]
        have h7 : y ^ 4 = Nat.factorial n + 57 := by 
          linarith [hxn, hy]
        have h8 : y ^ 4 % 5 = 2 := by 
          omega 
        omega 
    · -- Assume x = 81, prove x in A ∩ B
      intro hx
      rw [hx]
      constructor
      · -- Show 81 ∈ A
        use 4
        constructor
        · -- Show 4 > 0
          norm_num 
        · -- Calculate A 4
          rw [hA 4 (by norm_num)]
          all_goals norm_num [Nat.factorial] 
      · -- Show 81 ∈ B
        use 3
        all_goals norm_num 
  constructor
  · exact h1
  · exact h2