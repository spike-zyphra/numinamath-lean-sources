import Mathlib

/-Let $K$ be an integer which is a multiple of 99.
Find all three-digit numbers $n$, where $a$ is the hundreds digit, $b$ is the tens digit, and $c$ is the units digit,
such that $b$ is the geometric mean of $a$ and $c$ (i.e., $b^2 = ac$).
Also, if the number formed by swapping the hundreds and units digits of $n$ (let this be $n' = 100c+10b+a$) is subtracted from $n$,
the difference is $K$. Specifically, if $K=495$, show that the numbers are $500$ and $964$-/

theorem number_theory_641986: {n: ℤ | ∃ a b c, 0 < a ∧ a < 10 ∧ 0 ≤ b ∧ b < 10 ∧ 0 ≤ c ∧ c < 10 ∧
  n = 100 * a + 10 * b + c ∧ b ^ 2 = a * c ∧ n - (100 * c + 10 * b + a) = 495} = {500, 964} := by
    ext n
    constructor

    -- the forward direction
    .
      intro h
      simp
      rw [Set.mem_setOf] at h
      obtain ⟨a, b, c, la, ra, lb, rb, lc, rc, h1, h2, h3⟩ := h
      simp [h1] at h3
      rw [show 100 * a + 10 * b + c - (100 * c + 10 * b + a) = 99 * (a - c) by ring] at h3
      replace h3: a - c = 5 := by
        clear *- h3
        omega
      replace h3: a = c + 5 := by omega
      simp [h3] at *
      ring_nf at h1
      suffices c = 0 ∧ b = 0 ∨ c = 4 ∧ b = 6 by
        omega
      clear h1 h3 la rc
      replace ra: c < 5 := by omega
      have u: IsSquare ((c + 5) * c) := by
        rw [← h2]
        apply IsSquare.sq
      by_contra! ne
      interval_cases c
      all_goals absurd u; try native_decide
      .
        absurd ne
        simp
        simp at h2
        omega

      .
        absurd ne
        simp
        simp at h2
        replace h2: (b - 6) * (b + 6) = 0 := by nlinarith
        simp at h2
        omega


    -- the backward direction
    .
      intro h
      simp at h
      rcases h with h | h
      .
        rw [Set.mem_setOf, h]
        use 5, 0, 0
        norm_num
      .
        rw [Set.mem_setOf, h]
        use 9, 6, 4
        norm_num