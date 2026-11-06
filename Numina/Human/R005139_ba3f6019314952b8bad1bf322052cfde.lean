import Mathlib

def is_Jananess (n : ℕ) : Prop :=
  ∃ d1 d2 d3, 1 ≤ d1 ∧ d1 < d2 ∧ d2 < d3 ∧ d1 + d2 + d3 = 2022 ∧
    d1 ∣ n ∧ d2 ∣ n ∧ d3 ∣ n

/- On dit qu'un entier $n \geqslant 1$ est nippon s'il admet trois diviseurs
$d_{1}, d_{2}$ et $d_{3}$ tels que $1 \leqslant d_{1} < d_{2} < d_{3}$ et $d_{1}+d_{2}+d_{3}=2022$.
Quel est le plus petit entier nippon? -/

theorem number_theory_605742:
    IsLeast {n | 1 ≤ n ∧ is_Jananess n} 1344 := by

    constructor

    -- the forward direction
    .
      simp only [is_Jananess, Set.mem_setOf_eq]
      refine ⟨(by norm_num), ?_⟩
      use 6, 672, 1344
      omega

    -- the backward direction
    .
      intro n h
      simp only [is_Jananess, Set.mem_setOf_eq] at h
      rcases h with ⟨ln, h⟩
      rcases h with ⟨d1, d2, d3, l1, l2, l3, h, h1, h2, h3⟩
      apply exists_eq_mul_right_of_dvd at h1
      obtain ⟨a1, h1⟩ := h1
      apply exists_eq_mul_right_of_dvd at h2
      obtain ⟨a2, h2⟩ := h2
      apply exists_eq_mul_right_of_dvd at h3
      obtain ⟨a3, h3⟩ := h3
      by_contra! g
      have r1: a1 ≤ n := by
        clear *- l1 h1
        nlinarith
      have r2: a2 < a1 := by
        have y: a2 ≠ 0 := by
          by_contra! y
          simp [y] at h2
          simp [h2] at ln
        clear *- l2 h2 l1 h1 y
        have x: a2 ≤ a1 := by
          nlinarith
        suffices a2 ≠ a1 by omega
        by_contra! z
        simp [z] at h2
        rw [h1] at h2
        have r: a1 ≠ 0 := by omega
        replace h2: d1 = d2 := by
          apply Nat.mul_right_cancel at h2
          tauto
          omega
        linarith
      have r3: a3 < a2 := by
        clear *- l3 h3 l2 h2 ln
        have y: a3 ≠ 0 := by
          by_contra! y
          simp [y] at h3
          simp [h3] at ln
        have x: a3 ≤ a2 := by
          nlinarith
        suffices a3 ≠ a2 by omega
        by_contra! z
        simp [z] at h3
        rw [h2] at h3
        have r: a2 ≠ 0 := by omega
        replace h3: d2 = d3 := by
          apply Nat.mul_right_cancel at h3
          tauto
          omega
        linarith

      -- we show that a3 must be 1
      have s1: a3 = 1 := by
        have o: a3 ≠ 0 := by
          by_contra! o
          simp [o] at h3
          simp [h3] at ln
        suffices a3 < 2 by
          omega
        by_contra! s
        have f1: 2 * d1 ≤ n := by
          rw [h1]
          nlinarith
        have f2: 2 * d2 ≤ n := by
          rw [h2]
          nlinarith
        have f3: 2 * d3 ≤ n := by
          rw [h3]
          nlinarith
        have q: 2 * (d1 + d2 + d3) ≤ 3 * n := by
          clear *- f1 f2 f3
          omega
        simp [h] at q
        clear *- g q
        omega

      simp [s1] at *
      simp [← h3] at *

      -- then we show that a2 is at most 3
      have s2: a2 < 4 := by
        by_contra! s
        have f1: 4 * d1 ≤ n := by
          rw [h1]
          nlinarith
        have f2: 4 * d2 ≤ n := by
          rw [h2]
          nlinarith
        have q: 4 * (d1 + d2) ≤ 2 * n := by
          clear *- f1 f2
          omega
        replace q: 2 * (d1 + d2) ≤ n := by
          clear *- q
          omega
        clear *- h q g
        nlinarith

      -- hence a2 is either 2 or 3
      replace s2: a2 = 2 ∨ a2 = 3 := by
        omega
      rcases s2 with i | i

      -- case a2 = 2
      .
        simp [i] at *
        replace h: d2 * 2 + 2 * n + 2 * d1 = 4044 := by
          clear *- h
          omega
        rw [← h2] at h
        clear l3 s1 h3 r1
        ring_nf at h
        have f: d1 ∣ 4044 := by
          rw [← h]
          apply Nat.dvd_add
          .
            suffices d1 ∣ n by
              have u: n ∣ n * 3 := by simp
              apply Nat.dvd_trans this u
            rw [h1]
            simp
          .
            simp
        have u: d1 ∈ Nat.divisors 4044 := by
          simp [f]
        rw [show Nat.divisors 4044 = {1, 2, 3, 4, 6, 12, 337, 674, 1011, 1348, 2022, 4044}
        by native_decide] at u
        simp at u
        rcases u with u | u | u | u | u | u | u | u | u | u | u | u
        all_goals try omega
        simp [u] at h
        replace h: n = 1340 := by omega
        simp [h, u] at h1
        replace h1: 12 ∣ 1340 := by
          rw [h1]
          simp
        norm_num at h1

      -- case a2 = 3
      .
        simp [i] at *
        replace h: d2 * 3 + 3 * n + 3 * d1 = 6066 := by
          clear *- h
          omega
        rw [← h2] at h
        clear l3 s1 h3 r1
        ring_nf at h
        have f: d1 ∣ 6066 := by
          rw [← h]
          apply Nat.dvd_add
          .
            suffices d1 ∣ n by
              have u: n ∣ n * 4 := by simp
              apply Nat.dvd_trans this u
            rw [h1]
            simp
          .
            simp
        have u: d1 ∈ Nat.divisors 6066 := by
          simp [f]
        rw [show Nat.divisors 6066 = {1, 2, 3, 6, 9, 18, 337, 674, 1011, 2022, 3033, 6066} by native_decide] at u
        simp at u
        rcases u with u | u | u | u | u | u | u | u | u | u | u | u
        all_goals try omega