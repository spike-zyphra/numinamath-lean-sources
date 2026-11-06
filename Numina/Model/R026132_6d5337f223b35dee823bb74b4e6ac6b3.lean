import Mathlib

theorem number_theory_5410 (s : Set ℕ) (hs : s = {k : ℕ | ∃ m n, Nat.Prime m ∧ Nat.Prime n ∧ 4 * m + 9 * n = 111 ∧ k = m + n}) : ∑ᶠ k ∈ s, k = 14 := by
  have h1 : s = {14} := by
    ext k
    simp only [hs, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- First, if k ∈ s, then k = 14
      rintro ⟨m, n, hm, hn, heq, hk⟩
      by_cases h : n ≤ 11
      · -- Let's check each prime possible for n
        interval_cases n <;> try { 
          norm_num at hn heq
          all_goals try {
            have : m ≤ 27 := by
              omega
            interval_cases m <;> norm_num at hm heq
            all_goals
              omega
          }
        }
      · -- n > 11
        have : n ≥ 12 := by omega
        have h2 : 9 * n ≥ 108 := by
          omega
        have h4 : 4 * m ≤ 3 := by
          omega
        have : m < 1 := by
          omega
        have h7 : Nat.Prime m := hm
        have h8 : m = 0 := by omega
        rw [h8] at hm
        norm_num at hm
    · -- Now, if k = 14 in s
      intro hk
      rw [hk]
      use 3, 11
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      all_goals
        norm_num
  rw [h1]
  simp