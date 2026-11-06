import Mathlib

-- Any prime number p is at least 2
lemma le_prime {p: ℕ} (hp: Nat.Prime p): 2 ≤ p := by
  by_contra! o
  interval_cases p
  all_goals norm_num at hp

-- three consecutive prime numbers must be 3, 5 and 7
lemma lemma_1 {p: ℕ} (l: 2 ≤ p) (h1: Nat.Prime (p - 2)) (h2: Nat.Prime p) (h3: Nat.Prime (p + 2)): p = 5 := by

  -- note that one is multiple of 3
  have c: 3 ∣ p ∨ 3 ∣p + 1 ∨ 3 ∣ p + 2 := by omega
  rcases c with c | c | c

  -- 3 ∣ p
  .
    rw [Nat.prime_dvd_prime_iff_eq] at c
    simp [← c] at h1
    norm_num at h1
    norm_num
    exact h2

  -- 3 ∣ p + 1
  .
    replace c: 3 ∣ p - 2 := by
      rw [show p - 2 = p + 1 - 3 by omega]
      apply Nat.dvd_sub
      omega
      exact c
      simp
    rw [Nat.prime_dvd_prime_iff_eq] at c
    omega
    norm_num
    exact h1

  -- 3 ∣ p + 2
  .
    rw [Nat.prime_dvd_prime_iff_eq] at c
    replace c: p = 1 := by omega
    simp [c] at l
    norm_num
    exact h3

/-Find all such prime numbers that are both the sum of two prime numbers and the difference of two prime numbers.-/

theorem number_theory_107768: {n: ℕ | Nat.Prime n ∧ ∃ p q r s, p ≤ q ∧ s ≤ r ∧ Nat.Prime p ∧ Nat.Prime q ∧
  Nat.Prime r ∧ Nat.Prime s ∧ n = p + q ∧ n = r - s} = {5} := by

  ext n
  constructor

  -- the forward direction
  .
    intro h
    simp only [Set.mem_setOf_eq] at h
    rcases h with ⟨hn, h⟩
    obtain ⟨p, q, r, s, l1, l2, hp, hq, hr, hs, h1, h2⟩ := h
    have lp:= le_prime hp
    have lq:= le_prime hq
    have ln: 4 ≤ n := by omega

    -- hence n must be odd
    have On: Odd n := by
      apply Nat.Prime.odd_of_ne_two
      exact hn
      omega

    -- then p must be 2
    have vp: p = 2 := by
      by_contra! o
      have op: Odd p := by
        apply Nat.Prime.odd_of_ne_two
        exact hp
        omega
      have oq: Odd q := by
        apply Nat.Prime.odd_of_ne_two
        exact hq
        omega
      have en: Even n := by
        rw [h1]
        rw [Nat.even_add']
        simp [op, oq]
      absurd en
      simp [On]
    simp [vp] at *

    --also we have s = 2
    have vs: s = 2 := by
      by_contra! o
      have os: Odd s := by
        apply Nat.Prime.odd_of_ne_two
        exact hs
        omega
      have or: Odd r := by
        apply Nat.Prime.odd_of_ne_two
        exact hr
        omega
      have en: Even n := by
        rw [h2]
        rw [Nat.even_sub']
        simp [os, or]
        omega
      absurd en
      simp [On]
    simp [vs] at *

    -- then we apply lemma_1
    replace h1: q = n - 2 := by omega
    rw [h1] at hq
    replace h2: r = n + 2 := by omega
    rw [h2] at hr
    exact lemma_1 (by linarith) hq hn hr


  -- the backward direction
  .
    intro h
    simp at h
    simp only [h, Set.mem_setOf_eq]
    norm_num
    use 2
    use 3
    norm_num
    use 7
    use 2
    norm_num