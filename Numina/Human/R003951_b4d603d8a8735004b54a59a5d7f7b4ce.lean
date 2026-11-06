import Mathlib

/-Let N=2019^2−1. How many positive factors of N ^ 2 do not divide N ? -/

theorem number_theory_224437 {N: ℕ} (h: N = 2019 ^ 2 - 1):
    {k: ℕ | k ∣ N ^ 2 ∧ ¬ k ∣ N}.encard = 157 := by

  -- count the number of divisors of N ^ 2
    have count_1: (Nat.divisors (N ^ 2)).card = 189 := by
      rw [Nat.card_divisors]
      rw [h]
      norm_num
      native_decide
      rw [h]
      norm_num

  -- count the number of divisors of N
    have count_2: (Nat.divisors N).card = 32 := by
      rw [Nat.card_divisors]
      rw [h]
      norm_num
      native_decide
      rw [h]
      norm_num
  
  -- we write the set as the difference of two simp ones
    have h_eq: {k: ℕ | k ∣ N ^ 2 ∧ ¬ k ∣ N} = Nat.divisors (N ^ 2) \ Nat.divisors N := by

        ext k
        constructor
        -- the forward direction: show that the set is a subset of the right-hand side
        .
          intro h
          simp at h
          rcases h with ⟨h1, h2⟩
          simp
          constructor
          .
            simp [h1]
            rw [h]
            norm_num
          .
            intro l
            simp [l] at h2
        -- the backward direction: verify that the right-hand side are true
        .
          intro h
          simp at h
          rcases h with ⟨h1, h2⟩
          rcases h1 with ⟨h1, hn⟩
          simp [h1]
          by_contra! l
          simp [l] at h2
          simp [h2] at hn

  -- finally, count the number
    rw [h_eq]
    rw [Set.encard_coe_eq_coe_finsetCard]
    rw [Finset.card_sdiff]
    .
      rw [count_1]
      rw [count_2]
      norm_num
    .
      intro k hk
      simp at hk
      rcases hk with ⟨h1, h2⟩
      simp
      constructor
      .
        have o: N ∣ N ^ 2 := by
          rw [show N ^ 2 = N * N by ring]
          simp
        apply dvd_trans h1 o
      .
        exact h2
        