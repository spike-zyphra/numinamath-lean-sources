import Mathlib

/-Let $k$ be an integer chosen from $\{1, 2, 3, 4\}$. Let $P$ be a prime digit chosen from $\{2, 3, 5, 7\}$.
Let $S_1$ be the sum of all four-digit natural numbers $n$ such that:
1. $n$ is divisible by 45.
2. The tens digit of $n$ is $k$ times the hundreds digit of $n$.
(A four-digit number must be between 1000 and 9999, inclusive. Digits must be between 0 and 9.)

Let $S_2$ be the sum of all three-digit natural numbers $m$ such that:
1. $m$ is divisible by 18.
2. The hundreds digit of $m$ is $P$.
(A three-digit number must be between 100 and 999, inclusive.)

This problem asks for the value $S_1 - S_2$.
Show that for $k=2$ and $P=5$, the value $S_1 - S_2$ is 49131.-/

theorem number_theory_638737 (S1 S2: ℕ)
  (h1: S1 = ∑ᶠ n ∈ {n: ℕ | 45 ∣ n ∧
    ∃ a b c d, 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ d ≤ 9 ∧ c = 2 * b ∧ n = 1000 * a + 100 * b + 10 * c + d}, n)
  (h2: S2 = ∑ᶠ m ∈ {m: ℕ | 18 ∣ m ∧
    ∃ a b c, 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ a = 5 ∧ m = 100 * a + 10 * b + c}, m): S1 - S2 = 49131 := by

  -- we compute S1
  have f1: S1 = 52425 := by
    clear h2
    have h_eq: {n: ℕ | 45 ∣ n ∧
    ∃ a b c d, 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ d ≤ 9 ∧ c = 2 * b ∧ n = 1000 * a + 100 * b + 10 * c + d} =
      {4005, 1125, 7245, 4365, 1485, 9000, 6120, 3240, 9360, 6480} := by
      clear h1
      ext n
      constructor

      -- the forward direction
      .
        intro h
        simp only [Set.mem_setOf_eq] at h
        simp
        obtain ⟨h1, a, b, c, d, la, ra, rb, rc, rd, h2, h3⟩ := h
        simp [h2] at *
        rw [h3] at h1
        replace h1: 45 ∣ 10 * a + 30 * b + d := by
          rw [show 10 * a + 30 * b + d = 1000 * a + 100 * b + 10 * (2 * b) + d - 45 * (22 * a + 2 * b) by
            omega]
          apply Nat.dvd_sub
          .
            omega
          .
            tauto
          .
            simp
        ring_nf at h3
        have s: 5 ∣ d := by
          rw [show d = 10 * a + 30 * b + d - 5 * (2 * a + 6 * b) by omega]
          replace h1: 5 ∣ 10 * a + 30 * b + d := by
            suffices 5 ∣ 45 by
              apply dvd_trans this h1
            norm_num
          apply Nat.dvd_sub
          .
            omega
          .
            tauto
          .
            simp
        replace s: d = 5 ∨ d = 0 := by
          clear *- rd s
          omega
        rcases s with rfl | rfl

        -- case1: d = 5
        .
          omega

        -- case2: d = 0
        .
          omega

      -- the backward direction
      .
        intro h
        simp at h
        rcases h with h | h | h | h | h | h | h | h | h | h
        .
          simp only [Set.mem_setOf_eq, h]
          refine ⟨(by norm_num), ?_⟩
          use 4, 0, 0, 5
          norm_num
        .
          simp only [Set.mem_setOf_eq, h]
          refine ⟨(by norm_num), ?_⟩
          use 1, 1, 2, 5
          norm_num
        .
          simp only [Set.mem_setOf_eq, h]
          refine ⟨(by norm_num), ?_⟩
          use 7, 2, 4, 5
          norm_num
        .
          simp only [Set.mem_setOf_eq, h]
          refine ⟨(by norm_num), ?_⟩
          use 4, 3, 6, 5
          norm_num
        .
          simp only [Set.mem_setOf_eq, h]
          refine ⟨(by norm_num), ?_⟩
          use 1, 4, 8, 5
          norm_num
        .
          simp only [Set.mem_setOf_eq, h]
          refine ⟨(by norm_num), ?_⟩
          use 9, 0, 0, 0
          norm_num
        .
          simp only [Set.mem_setOf_eq, h]
          refine ⟨(by norm_num), ?_⟩
          use 6, 1, 2, 0
          norm_num
        .
          simp only [Set.mem_setOf_eq, h]
          refine ⟨(by norm_num), ?_⟩
          use 3, 2, 4, 0
          norm_num
        .
          simp only [Set.mem_setOf_eq, h]
          refine ⟨(by norm_num), ?_⟩
          use 9, 3, 6, 0
          norm_num
        .
          simp only [Set.mem_setOf_eq, h]
          refine ⟨(by norm_num), ?_⟩
          use 6, 4, 8, 0
          norm_num

    -- then sum the numbers up
    rw [h_eq] at h1
    rw [h1]
    clear h_eq h1
    rw [finsum_mem_eq_toFinset_sum]
    simp


  -- we compute S2
  have f2: S2 = 3294 := by
    clear h1 f1
    have h_eq: {m: ℕ | 18 ∣ m ∧
    ∃ a b c, 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ a = 5 ∧ m = 100 * a + 10 * b + c} =
      {540, 522, 504, 594, 576, 558} := by
      clear h2
      ext m
      constructor

      -- the forward direction
      .
        intro h
        simp only [Set.mem_setOf_eq] at h
        simp
        obtain ⟨h1, a, b, c, la, ra, rb, rc, h2, h3⟩ := h
        omega

      -- the backward direction
      .
        intro h
        simp at h
        rcases h with h | h | h | h | h | h
        .
          simp only [Set.mem_setOf_eq, h]
          refine ⟨(by norm_num), ?_⟩
          use 5, 4, 0
          norm_num
        .
          simp only [Set.mem_setOf_eq, h]
          refine ⟨(by norm_num), ?_⟩
          use 5, 2, 2
          norm_num
        .
          simp only [Set.mem_setOf_eq, h]
          refine ⟨(by norm_num), ?_⟩
          use 5, 0, 4
          norm_num
        .
          simp only [Set.mem_setOf_eq, h]
          refine ⟨(by norm_num), ?_⟩
          use 5, 9, 4
          norm_num
        .
          simp only [Set.mem_setOf_eq, h]
          refine ⟨(by norm_num), ?_⟩
          use 5, 7, 6
          norm_num
        .
          simp only [Set.mem_setOf_eq, h]
          refine ⟨(by norm_num), ?_⟩
          use 5, 5, 8
          norm_num

    -- then sum the numbers up
    rw [h_eq] at h2
    rw [h2]
    clear h_eq h2
    rw [finsum_mem_eq_toFinset_sum]
    simp


  -- then we compute S1 - S2
  simp [f1, f2]
