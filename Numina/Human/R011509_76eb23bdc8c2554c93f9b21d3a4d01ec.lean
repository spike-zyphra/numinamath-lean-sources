import Mathlib

/-Six consecutive prime numbers have sum p.
Given that p is also prime, determine all possible values of p.-/

theorem number_theory_256956: {p: ℕ | Nat.Prime p ∧
  ∃ a b c d e f: ℕ, Nat.Prime a ∧ Nat.Prime b ∧ Nat.Prime c ∧ Nat.Prime d ∧ Nat.Prime e ∧ Nat.Prime f ∧
  a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < f ∧ a + b + c + d + e + f = p ∧
  ∀ x, Nat.Prime x ∧ a < x ∧ x < f → x = b ∨ x = c ∨ x = d ∨ x = e} = {41} := by

    ext p
    constructor
    -- show p is the unique solution
    .
      intro h
      simp only [Set.mem_setOf_eq] at h
      rcases h with ⟨hp, h⟩
      obtain ⟨a, b, c, d, e, f, ha, hb, hc, hd, he, hf, hab, hbc, hcd, hde, hef, h, s⟩ := h
      simp

      -- we show that a = 2
      have ia: a = 2 := by
        clear s
        by_contra! o
        replace o: 3 ≤ a:= by
          by_contra! n
          have t: a = 0 ∨ a = 1 := by omega
          rcases t with t | t
          .
            simp [t] at ha
            norm_num at ha
          .
            simp [t] at ha
            norm_num at ha
        -- then a b c d e f are all odd
        have oa: a % 2 = 1 := by
          have ia: Odd a := by
            apply Nat.Prime.odd_of_ne_two
            exact ha
            omega
          apply Odd.not_two_dvd_nat at ia
          omega
        have ob: b % 2 = 1 := by
          have ib: Odd b := by
            apply Nat.Prime.odd_of_ne_two
            exact hb
            omega
          apply Odd.not_two_dvd_nat at ib
          omega
        have oc: c % 2 = 1 := by
          have ic: Odd c := by
            apply Nat.Prime.odd_of_ne_two
            exact hc
            omega
          apply Odd.not_two_dvd_nat at ic
          omega
        have od: d % 2 = 1 := by
          have id: Odd d := by
            apply Nat.Prime.odd_of_ne_two
            exact hd
            omega
          apply Odd.not_two_dvd_nat at id
          omega
        have oe: e % 2 = 1 := by
          have ie: Odd e := by
            apply Nat.Prime.odd_of_ne_two
            exact he
            omega
          apply Odd.not_two_dvd_nat at ie
          omega
        have of: f % 2 = 1 := by
          have If: Odd f := by
            apply Nat.Prime.odd_of_ne_two
            exact hf
            omega
          apply Odd.not_two_dvd_nat at If
          omega
        have h':= h
        replace h: (a + b + c + d + e + f) % 2 = p % 2 := by
          rw [h]
        simp [oa,ob,oc,od,oe,of,Nat.add_mod] at h
        replace h: 2 ∣ p := by
          apply Nat.dvd_of_mod_eq_zero
          rw [h]
        rw [Nat.prime_dvd_prime_iff_eq] at h
        rw [← h] at hp
        nlinarith
        norm_num
        exact hp

      simp [ia] at *

      -- we show that b = 3
      have ib: b = 3 := by
        by_contra! o
        specialize s 3
        norm_num at s
        have lf: 3 < f := by omega
        simp [lf] at s
        omega
      simp [ib] at *
      clear ha hb hab ia ib

      -- we show that c = 5
      have ic: c = 5 := by
        by_contra! o
        specialize s 5
        norm_num at s
        have lf: 5 < f := by omega
        simp [lf] at s
        have v: c ≠ 4 := by
          by_contra! n
          simp [n] at hc
          norm_num at hc
        omega
      simp [ic] at *
      clear hc ic hbc

      -- we show that d = 7
      have id: d = 7 := by
        by_contra! o
        specialize s 7
        norm_num at s
        have lf: 7 < f := by omega
        simp [lf] at s
        have v: d ≠ 6 := by
          by_contra! n
          simp [n] at hd
          norm_num at hd
        omega
      simp [id] at *
      clear hd id hcd

      -- we show that e = 11
      have ie: e = 11 := by
        by_contra! o
        specialize s 11
        norm_num at s
        have lf: 11 < f := by
          by_contra! n
          have sf: 8 < f := by omega
          interval_cases f
          all_goals norm_num at hf
          have se: e < 11 := by omega
          interval_cases e
          all_goals norm_num at he
        simp [lf] at s
        simp [s] at o
      simp [ie] at *
      clear he ie hde

      -- we show that f = 13
      have nf: f = 13 := by
        by_contra! o
        specialize s 13
        norm_num at s
        interval_cases f
        .
          norm_num at hf
        .
          norm_num at o

      simp [nf] at h
      rw [h]


-- the backward direction
    .
      intro h
      simp at h
      simp [h]
      norm_num
      use 2
      norm_num
      use 3
      norm_num
      use 5
      norm_num
      use 7
      norm_num
      use 11
      norm_num
      use 13
      norm_num
      intro x h1 h2 h3
      interval_cases x
      all_goals norm_num at h1
      all_goals omega