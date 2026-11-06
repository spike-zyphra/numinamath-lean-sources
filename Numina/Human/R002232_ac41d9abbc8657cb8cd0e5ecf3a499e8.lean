import Mathlib

/-What is the smallest non-square positive integer that is the product of four prime numbers (not necessarily distinct)?-/

-- we show that any prime is at least 2
lemma twp_le_prime (n: ℕ) (h: Nat.Prime n): 2 ≤ n := by
  by_contra a
  simp at a
  interval_cases n
  .
    norm_num at h
  .
    norm_num at h

theorem number_theory_75160: IsLeast {n: ℕ | 0 < n ∧ ¬ IsSquare n ∧
  ∃ p q r s, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ Nat.Prime s ∧
  p ≤ q ∧ q ≤ r ∧ r ≤ s ∧ n = p * q * r * s} 24 := by

  constructor

  -- the forward direction
  .
    simp
    constructor
    .
      native_decide
    .
      use 2
      norm_num
      use 2
      norm_num
      use 2
      norm_num
      use 3
      norm_num

  -- the backward direction
  .
    intro n h
    simp only [Set.mem_setOf_eq] at h
    rcases h with ⟨ln, hn, h⟩
    obtain ⟨p, q, r, s, hp, hq, hr, hs, h1, h2, h3, h⟩ := h

    apply twp_le_prime at hp

    -- we show that 3 ≤ s
    have hs: 3 ≤ s := by
      by_contra! ls
      have vp: p = 2 := by omega
      have vq: q = 2 := by omega
      have vr: r = 2 := by omega
      have vs: s = 2 := by omega
      simp [vp, vq, vr, vs] at h
      simp [h] at hn
      absurd hn
      native_decide

    -- now 2 ≤ p, q, r  3 ≤ s, hence 24 ≤ n
    have lq: 2 ≤ q := by omega
    have lr: 2 ≤ r := by omega
    rw [h]
    have f1: 4 ≤ p * q := by
      nlinarith
    have f2: 8 ≤ p * q * r := by
      nlinarith
    nlinarith