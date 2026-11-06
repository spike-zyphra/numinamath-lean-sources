import Mathlib

def three_stars (n: ℕ): Prop :=
  100 ≤ n ∧ n < 1000 ∧
  ∃ p q r: ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
    p < q ∧ q < r ∧ n = p * q * r

lemma two_le_of_prime (n: ℕ) (h: Nat.Prime n): 2 ≤ n := by
  by_contra! l
  interval_cases n
  all_goals norm_num at h

lemma lemma_2 (p q: ℕ) (hp: Nat.Prime p) (hq: Nat.Prime q) (ne: p ≠ q): Nat.Coprime p q := by
    rw [Nat.Prime.coprime_iff_not_dvd]
    .
      by_contra! s
      rw [Nat.prime_dvd_prime_iff_eq] at s
      tauto
      exact hp
      exact hq
    .
      exact hp

/-We say that a positive three-digit integer is three stars if it is the result of the product of three distinct prime numbers.
For example, 286=2⋅11⋅13 is a three-star number, but
30=2⋅3⋅5 and 275=5⋅5⋅13 are not three-star numbers,
as the first has only two digits and the second is not the product of three distinct primes.
(a) What is the smallest three-star number?
(b) Show that each three-star number has some common divisor with 30 greater than 1.-/

theorem number_theory_255479: IsLeast {n: ℕ | three_stars n} 102 ∧ ∀ k, three_stars k → 1 < k.gcd 30 := by

  constructor

  -- the first part (a)
  .
    constructor

    -- show 102 is a three-star number
    .
      simp [three_stars]
      use 2
      norm_num
      use 3
      norm_num
      use 17
      norm_num

    -- show 102 is the least three-star number
    .
      intro n h
      simp [three_stars] at h
      obtain ⟨ln, rn, p, hp, q, hq, r, hr, l1, l2, h⟩ := h
      by_contra! l
      interval_cases n

      -- show 100 is not a three-star number
      .
        have f: 2 ∣ p * q * r := by
          rw [← h]
          norm_num
        have vp: p = 2 := by
          by_contra! s
          have t:= two_le_of_prime p hp
          replace s: 3 ≤ p := by omega
          rw [show p * q * r = p * (q * r) by ring] at f
          apply Nat.Coprime.dvd_of_dvd_mul_left at f
          apply Nat.Coprime.dvd_of_dvd_mul_left at f
          rw [show r = r * 1 by ring] at f
          apply Nat.Coprime.dvd_of_dvd_mul_left at f
          norm_num at f

          -- we apply lemma_2 to show that 2 and p,q,r are coprime
          exact lemma_2 2 r (by norm_num) hr (by omega)
          exact lemma_2 2 q (by norm_num) hq (by omega)
          exact lemma_2 2 p (by norm_num) hp (by omega)
        simp [vp] at h
        replace h: q * r = 50 := by nlinarith
        have vq: q = 2 := by
          by_contra! s
          have t:= two_le_of_prime q hq
          replace s: 3 ≤ q := by omega
          replace f: 2 ∣ q * r := by
            rw [h]
            norm_num
          apply Nat.Coprime.dvd_of_dvd_mul_left at f
          rw [show r = r * 1 by ring] at f
          apply Nat.Coprime.dvd_of_dvd_mul_left at f
          norm_num at f

          -- we apply lemma_2 to show that 2 and p,q,r are coprime
          exact lemma_2 2 r (by norm_num) hr (by omega)
          exact lemma_2 2 q (by norm_num) hq (by omega)
        simp [vq] at h
        replace h: r = 25 := by nlinarith
        simp [h] at hr
        norm_num at hr

      -- show 101 is not a three-star number
      .
        have u: p ∣ 101 := by
          rw [h]
          rw [show p * q * r = p * (q * r) by ring]
          simp
        rw [Nat.prime_dvd_prime_iff_eq] at u
        simp [u] at h
        replace h: q * r = 1 := by nlinarith
        have lq: q ≤ 1 := by nlinarith
        linarith
        tauto
        norm_num


  -- the second part (b)
  .
    intro k h
    simp [three_stars] at h
    obtain ⟨ln, rn, p, hp, q, hq, r, hr, l1, l2, h⟩ := h
    by_contra! l
    replace l: k.gcd 30 = 1 := by
      suffices k.gcd 30 ≠ 0 by omega
      apply Nat.gcd_ne_zero_right
      norm_num
    rw [← Nat.coprime_iff_gcd_eq_one] at l

    -- then we splits the coprime into three parts
    have c1: k.Coprime 2 := by
      rw [show 30 = 2 * 15 by norm_num] at l
      apply Nat.Coprime.coprime_mul_right_right l
    have c2: k.Coprime 3 := by
      rw [show 30 = 3 * 10 by norm_num] at l
      apply Nat.Coprime.coprime_mul_right_right l
    have c3: k.Coprime 5 := by
      rw [show 30 = 5 * 6 by norm_num] at l
      apply Nat.Coprime.coprime_mul_right_right l

    -- then we show that 7 ≤ p
    have lp: 7 ≤ p := by
      by_contra! x
      have j:= two_le_of_prime p hp
      interval_cases p
      .
        rw [h] at c1
        have c: Nat.Coprime 2 2 := by
          rw [show 2 * q * r = 2 * (q * r) by ring] at c1
          apply Nat.Coprime.coprime_mul_right c1
        norm_num at c
      .
        rw [h] at c2
        have c: Nat.Coprime 3 3 := by
          rw [show 3 * q * r = 3 * (q * r) by ring] at c2
          apply Nat.Coprime.coprime_mul_right c2
        norm_num at c
      .
        rw [h] at c1
        have c: Nat.Coprime 2 2 := by
          rw [show 4 * q * r = 2 * (2 * q * r) by ring] at c1
          apply Nat.Coprime.coprime_mul_right c1
        norm_num at c
      .
        rw [h] at c3
        have c: Nat.Coprime 5 5 := by
          rw [show 5 * q * r = 5 * (q * r) by ring] at c3
          apply Nat.Coprime.coprime_mul_right c3
        norm_num at c
      .
        rw [h] at c1
        have c: Nat.Coprime 2 2 := by
          rw [show 6 * q * r = 2 * (3 * q * r) by ring] at c1
          apply Nat.Coprime.coprime_mul_right c1
        norm_num at c

    -- then we show that 11 ≤ q
    have lq: 11 ≤ q := by
      by_contra! x
      have rq: 7 < q := by
        omega
      interval_cases q
      all_goals norm_num at hq

    -- then we show that 13 ≤ r
    have lr: 13 ≤ r := by
      by_contra! x
      have rr: 11 < r := by
        omega
      interval_cases r
      all_goals norm_num at hr
    absurd rn
    rw [h]
    simp
    clear *- lp lq lr
    have i: 77 ≤ p * q := by nlinarith
    nlinarith