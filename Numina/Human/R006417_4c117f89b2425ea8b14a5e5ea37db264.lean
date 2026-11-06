import Mathlib

/-E994 Let $M$ be a positive integer such that $M(M-1)/2$ is a perfect square.
When Yunji added all the integers from $1$ to $M$, she mistakenly left out a number $n$,
where $1 \le n \le M$. Her incorrect sum turned out to be a perfect square. Show that the number Yunji left out must be $M$.-/

theorem number_theory_636834 (M n: ℤ) (l1: 0 < M) (l2: 1 ≤ n ∧ n ≤ M) (h1: ∃ k, M * (M - 1) / 2 = k ^ 2)
  (h2: ∃ s, (M * (M + 1) / 2 - n) = s ^ 2): n = M := by

    replace h1: ∃ k, 0 ≤ k ∧ M * (M - 1) / 2 = k ^ 2 := by
      obtain ⟨k, hk⟩ := h1
      by_cases r: 0 ≤ k
      .
        use k
      .
        use -k
        constructor
        .
          linarith
        .
          rw [hk]
          simp
    replace h2: ∃ s, 0 ≤ s ∧ (M * (M + 1) / 2 - n) = s ^ 2 := by
      obtain ⟨s, hs⟩ := h2
      by_cases r: 0 ≤ s
      .
        use s
      .
        use -s
        constructor
        .
          linarith
        .
          rw [hs]
          simp

    obtain ⟨k, hk, h1⟩ := h1
    obtain ⟨s, hs, h2⟩ := h2
    by_contra! ne
    rcases l2 with ⟨l2, l3⟩
    replace l3: n ≤ M - 1 := by
      omega

    -- we first remove the demominators
    have d: 2 ∣ M * (M - 1) := by
      rw [Int.dvd_iff_emod_eq_zero]
      rw [Int.mul_emod]
      by_cases r: M % 2 = 0
      .
        simp [r]
      .
        simp at r
        suffices (M - 1) % 2 = 0 by
          simp [this]
        rw [Int.sub_emod]
        simp [r]
    have d2: 2 ∣ M * (M + 1) := by
      rw [Int.dvd_iff_emod_eq_zero]
      rw [Int.mul_emod]
      by_cases r: M % 2 = 0
      .
        simp [r]
      .
        simp at r
        suffices (M + 1) % 2 = 0 by
          simp [this]
        rw [Int.add_emod]
        simp [r]
    replace h1: M * (M - 1) = 2 * k ^ 2 := by
      rw [← h1]
      symm
      apply Int.mul_ediv_cancel'
      tauto
    replace h2: M * (M + 1) - 2 * n = 2 * s ^ 2 := by
      rw [← h2]
      ring_nf
      suffices (M + M ^ 2) / 2 * 2 = M * (M + 1) by
        simp [this]
        ring
      rw [show M + M ^ 2 = M * (M + 1) by ring]
      apply Int.ediv_mul_cancel
      tauto
    clear d d2

    -- we show that s is at most k - 1
    have ls: s ≤ k - 1 := by
      by_contra! o
      replace o: k ≤ s := by omega
      by_cases f: k = s
      .
        rw [f] at h1
        rw [← h1] at h2
        replace h2: n = M := by nlinarith
        simp [h2] at l3

      .
        replace o: k + 1 ≤ s := by
          omega
        replace h2: 2 * (k + 1) ^ 2 ≤ M * (M + 1) := by nlinarith
        rw [show M * (M + 1) = M * (M - 1) + 2 * M by ring] at h2
        simp [h1] at h2
        have h3: 2 * k + 1 ≤ M := by nlinarith
        have v: 1 ≤ k := by
          suffices k ≠ 0 by omega
          by_contra! i
          simp [i] at h1
          rcases h1 with h1 | h1
          .
            simp [h1] at l1
          .
            simp [h1] at l3
            omega
        nlinarith

    -- finally, we tackle the case when s ≤ k - 1 by size argument
    replace h2: M * (M + 1) - 2 * (M - 1) ≤ 2 * s ^ 2 := by nlinarith
    replace h2: M * (M + 1) - 2 * (M - 1) ≤ 2 * (k - 1) ^ 2 := by
      nlinarith
    nlinarith