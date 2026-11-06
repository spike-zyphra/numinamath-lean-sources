import Mathlib

/-
The largest prime number less than 30 that can be written as the sum of two primes is
(A) 29
(B) 23
(C) 19
(D) 17
(E) 13
-/

open Nat

theorem  number_theorey_270574 : IsGreatest {p | p.Prime ∧ p < 30 ∧ ∃ q r : ℕ, p = q + r ∧ q.Prime ∧ r.Prime} 19 := by 
  unfold IsGreatest
  simp
  constructor

  -- First we verify that 19 satisfies all conditions:
  constructor
  norm_num
  use 17, 2
  simp
  norm_num

  --We check that 19 is an upper bound
  --We enumerate larger numbers. None of them can satisfy the assumptions.
  unfold upperBounds
  simp
  intro p pp pl30 q r h qp rp
  wlog rleq : r ≤ q
  push_neg at rleq
  have qler: q ≤ r := by linarith
  apply this
  exact pp
  exact pl30
  have perpq: p = r + q := by linarith
  exact perpq
  exact rp
  exact qp
  exact qler

  have re2: r = 2 := by 
    have : 2 ≤ r := by exact Prime.two_le rp
    by_contra rne2
    have rge3: 3 ≤ r := by omega
    have qge3: 3 ≤ q := by omega
    have : ¬ q = 2 := by linarith
    have npe2: ¬ p = 2 := by linarith

    have or: Odd r := by exact Prime.odd_of_ne_two rp rne2
    have oq: Odd q := by exact Prime.odd_of_ne_two qp this

    have : Even (q + r) := by exact Odd.add_odd oq or
    rw [←h] at this
    have pe2: p = 2 := by exact (Prime.even_iff pp).mp this
    linarith

  by_contra pge20
  have : 20 ≤ p := by omega
  
  by_cases pe : p = 20
  have : q = 18 := by linarith
  rw [this] at qp; norm_num at qp

  by_cases pe : p = 21
  rw [pe] at pp; norm_num at pp

  by_cases pe : p = 22
  rw [pe] at pp; norm_num at pp

  by_cases pe : p = 23
  have : q = 21 := by linarith
  rw [this] at qp; norm_num at qp

  by_cases pe : p = 24
  rw [pe] at pp; norm_num at pp

  by_cases pe : p = 25
  rw [pe] at pp; norm_num at pp

  by_cases pe : p = 26
  rw [pe] at pp; norm_num at pp

  by_cases pe : p = 27
  rw [pe] at pp; norm_num at pp

  by_cases pe : p = 28
  rw [pe] at pp; norm_num at pp

  by_cases pe : p = 29
  have : q = 27 := by linarith
  rw [this] at qp; norm_num at qp

  have pe : p = 30 := by omega
  rw [pe] at pp; norm_num at pp