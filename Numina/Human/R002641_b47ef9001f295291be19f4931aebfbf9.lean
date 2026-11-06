import Mathlib

open Nat
open Finset

/-
A positive integer n has 60 divisors and 7n has 80 divisors.
What is the greatest integer k such that 7^k divides n?
-/

theorem problem
    (n : ℕ)
    (hn : #n.divisors = 60)
    (hn2 : #(7*n).divisors = 80)
    -- Prove that the multiplicity of 7 in n is 2
    : n.factorization 7 = 2 := by
  have coprime_ordProj_ordCompl {p n : ℕ} (h : p.Prime) (hn : n ≠ 0)
      : Coprime (ordProj[p] n) (ordCompl[p] n) :=
    Coprime.pow_left (n.factorization p) (coprime_ordCompl h hn)

  -- The number of divisors of p^k is k + 1 if p is a prime number
  have divisors_ordProj_of_prime
      {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
      #(ordProj[p] n).divisors = n.factorization p + 1 := by
    by_cases hnp : n.factorization p = 0
    . simp [hnp]
    . have : ordProj[p] n ≠ 0 := by simp [hnp, hp.ne_zero]
      rw [card_divisors this]
      have : (ordProj[p] n).primeFactors = {p} := by rw [primeFactors_prime_pow hnp hp]
      simp [this, hp]

  -- If one decomposes n = p^k * m with p prime not dividing m,
  -- then d(n) = d(p^k) * d(m) = (k + 1) * d(m)
  have h0 (n) (n_ne_0 : n ≠ 0) (p : ℕ) (hp : p.Prime)
      : #n.divisors = (n.factorization p + 1) * #(ordCompl[p] n).divisors := by
    have := coprime_ordProj_ordCompl hp n_ne_0
    have := Coprime.card_divisors_mul this
    have this2 : (ordProj[p] n) * (ordCompl[p] n) = n := ordProj_mul_ordCompl_eq_self n p
    rw [this2] at this
    have this2 : #(ordProj[p] n).divisors = n.factorization p + 1 := by
      exact divisors_ordProj_of_prime hp n_ne_0
    rw [this2] at this
    exact this
  have n_ne_0 : n ≠ 0 := by
    intro this
    simp [this] at hn

  have prime_7 : (7).Prime := by decide
  -- If n = 7^k * m with 7 not dividing m, d(n) = (k + 1) * d(m)  and d(7 * n) = (k + 2) * d(m)
  have this1 := h0 n n_ne_0 7 prime_7
  have this2 := h0 (7*n) (by simp [n_ne_0]) 7 prime_7
  have : (7 * n).factorization 7 = n.factorization 7 + 1 := by
    simp [n_ne_0, prime_7]
    ring
  rw [this] at this2
  have : 7 ^ (n.factorization 7 + 1) = 7 * 7 ^ n.factorization 7 := by ring
  rw [this] at this2
  have : (7 * n / (7 * 7 ^ n.factorization 7)) = n / 7 ^ n.factorization 7 := by
    rw [Nat.mul_div_mul_left _ _ (by norm_num)]
  rw [this] at this2
  -- From assumptions, 60 = (k + 1) * d(m) and 80 = (k + 2) * d(m)
  rw [hn] at this1
  rw [hn2] at this2
  -- Solve for the value of k thanks to these equations
  let z := (n.factorization 7 + 1) * (n.factorization 7 + 1 + 1) * #(n / 7 ^ n.factorization 7).divisors
  have this1 : 60 * (n.factorization 7 + 1 + 1) = z := by
    have := congrArg (. * (n.factorization 7 + 1 + 1)) this1
    dsimp at this
    rw [this]
    ring
  have this2 : 80 * (n.factorization 7 + 1) = z := by
    have := congrArg (. * (n.factorization 7 + 1)) this2
    dsimp at this
    rw [this]
    ring
  linarith