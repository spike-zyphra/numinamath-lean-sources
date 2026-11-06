import Mathlib

/-Let $K$ and $M$ be positive integers. Determine the number of two-digit natural numbers $N$
(i.e., integers $N$ such that $10 \le N \le 99$) such that $N = K \times S(N+M)$,
where $S(x)$ denotes the sum of the digits of $x$ in base 10. For $K=6$ and $M=7$, show that the answer is 2.-/

theorem number_theory_635201: {N: ℕ | ∃ a b, N = 10 * a + b ∧ 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧
  ((b ≤ 2 ∧ N = 6 * (a + b + 7)) ∨ (a ≤ 8 ∧ 3 ≤ b ∧ N = 6 * (a + b + 7 - 9))
    ∨ (a = 9 ∧ 3 ≤ b ∧ N = 6 * (a + b + 7 - 18)))}.encard = 2 := by

  -- we directly compute all possible two-digit numbers
  have h_eq: {N: ℕ | ∃ a b, N = 10 * a + b ∧ 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧
  ((b ≤ 2 ∧ N = 6 * (a + b + 7)) ∨ (a ≤ 8 ∧ 3 ≤ b ∧ N = 6 * (a + b + 7 - 9))
    ∨ (a = 9 ∧ 3 ≤ b ∧ N = 6 * (a + b + 7 - 18)))} = {24, 78} := by
    ext N
    constructor

    -- the forward direction
    .
      intro h
      simp only [Set.mem_setOf_eq] at h
      simp
      obtain ⟨a, b, hn, la, ra, rb, h⟩ := h
      rcases h with h | h | h

      -- case1: not carry
      .
        rcases h with ⟨la, h⟩
        omega

      -- case2: carry, but not from 9
      .
        rcases h with ⟨la, h⟩
        omega

      -- case3: carry from 9
      .
        rcases h with ⟨la, h⟩
        omega

    -- the backward direction
    .
      intro h
      simp at h
      rcases h with h | h
      .
        simp [h]
        use 2, 4
        norm_num
      .
        simp [h]
        use 7, 8
        norm_num


  -- then we can compute the encard
  rw [h_eq]
  simp [Set.encard]
