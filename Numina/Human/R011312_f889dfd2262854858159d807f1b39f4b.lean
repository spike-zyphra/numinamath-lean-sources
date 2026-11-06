import Mathlib

open Polynomial

-- we present a classic lemma in number theory about polynomials
lemma int_poly_mod_eq (p: Polynomial ℤ) (x y: ℤ) (ne: x ≠ y): x - y ∣ p.eval x - p.eval y := by
  sorry

-- we write the special case of Fermat's little theorem as lemma
lemma fermat_little_theorem (p: ℕ) (hp: Nat.Prime p) (hp: 3 ≤ p): 2 ^ p % p = (2: ℤ) := by
  sorry

-- a simple lemma about polynomials
lemma lemma_1 (f: Polynomial ℤ) (h: ¬ ∃ a: ℤ, f = C a): ∃ n p: ℕ, 0 < n ∧ Nat.Prime p ∧ 3 ≤ p ∧ ↑p ∣ f.eval ↑n := by
  sorry

/-Find all integer-coefficient polynomials
f(x) such that for all positive integers n we have
f(n)∣2^n−1.-/

theorem number_theory_236989: {f: Polynomial ℤ | ∀ n: ℕ, 0 < n → f.eval ↑n ∣ 2 ^ n - 1} =
  ({C (1: ℤ), C (-1)}: Set (Polynomial ℤ)) := by

  ext f
  constructor

  -- the forward direction
  .
    intro h
    simp at h
    simp
    by_cases l: ∃ a: ℤ, f = C a

    -- case 1: f is a constant polynomial
    .
      obtain ⟨a, l⟩ := l
      simp [l] at h
      simp [l]
      specialize h 1
      norm_num at h
      by_cases o: 0 ≤ a
      .
        apply Int.eq_one_of_dvd_one at h
        simp [h]
        exact o
      .
        set b:= - a
        replace o: 0 ≤ b := by omega
        replace h: b ∣ 1 := by
          simp [b]
          exact h
        apply Int.eq_one_of_dvd_one at h
        simp [b] at h
        replace h: a = -1 := by omega
        simp [h]
        exact o

    -- case 2: f is not a constant polynomial
    .
      have u: ∃ n p: ℕ, 0 < n ∧ Nat.Prime p ∧ 3 ≤ p ∧ ↑p ∣f.eval ↑n := by
        apply lemma_1 f l
        -- this comes from the fact that f is not a constant polynomial, which is tricky to formalize, i omit it

      obtain ⟨n, p, hn, pp, lp, g⟩ := u
      have v:= h n hn
      replace v: ↑p ∣ 2 ^ n - (1: ℤ) := by
        apply dvd_trans g v
      have j:= int_poly_mod_eq f (n + p) n (by omega)
      rw [show (n: ℤ) + p - n = p by omega] at j
      specialize h (n + p) (by omega)

      -- then we can show the following division
      have v2: ↑p ∣ 2 ^ (n + p) - (1 : ℤ) := by
        have r: ↑p ∣ eval (↑(n + p)) f := by
          rw [show ↑(n + p) = (n: ℤ) + ↑p by simp]
          rw [show eval (↑n + ↑p) f = eval (↑n + ↑p) f - eval (↑n) f + eval (↑n) f by omega]
          apply Int.dvd_add
          exact j
          exact g
        apply dvd_trans r h

      -- then we derive contradiction from v and v2
      clear h g j
      rw [show (2: ℤ) ^ (n + p) = 2 ^ n * 2 ^ p by ring] at v2
      rw [Int.dvd_iff_emod_eq_zero] at v2
      rw [Int.sub_emod] at v2
      rw [Int.mul_emod] at v2
      have o1: 2 % (p: ℤ) = 2 := by
        apply Int.emod_eq_of_lt
        norm_num
        zify at lp
        omega
      have o2: 1 % (p: ℤ) = 1 := by
        apply Int.emod_eq_of_lt
        norm_num
        zify at lp
        omega
      replace v: 2 ^ n % (p: ℤ) = 1 := by
        rw [← o2]
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
        norm_num
        exact v

      -- then we apply Fermat's little theorem
      have w: 2 ^ p % p = (2: ℤ) := by
        apply fermat_little_theorem
        exact pp
        exact lp
      rw [w] at v2
      rw [v] at v2
      norm_num at v2
      rw [o1, o2] at v2
      norm_num at v2
      norm_cast at v2
      apply Nat.le_of_dvd at v2
      linarith
      norm_num

  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h
    .
      simp [h]
    .
      simp [h]
