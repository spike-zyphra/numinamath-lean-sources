import Mathlib

open Nat

-- Mathlib don't have this.
lemma my_factorial_inj : 0 < a → 0 < b → a ! = b ! → a = b := by
  intro apos bpos H
  rcases a with _ | a
  . omega
  rcases a with _ | a
  . simp at *
    rcases b with _ | b
    . simp at bpos
    . simp [Nat.factorial] at H
      simp
      have : (b + 1) * b ! ≥ b + 1 := by
        refine Nat.le_mul_of_pos_right (b + 1) ?_
        exact factorial_pos b
      rw [←H] at this
      simp at this
      assumption
  . apply (Nat.factorial_inj ?_).mp
    assumption
    omega

-- Show the inequality by induction.
lemma lemma2 : (a + 2) ! * 2 < ((a + 2) * 2)! := by
  induction a with
  | zero => decide
  | succ a ih =>
    ring_nf at *
    rw [show 3 + a = 2 + a + 1 by omega]
    simp [Nat.factorial]
    have ih : (2 + a)! * 2 * (2 + a + 1) < (4 + a * 2)! * (2 + a + 1)  := by
      refine Nat.mul_lt_mul_of_pos_right ih ?_
      simp
    calc
      _ < (4 + a * 2)! * (2 + a + 1) := by
        ring_nf at *;
        exact ih
      _ ≤ _ := ?_
    rw [show 6 + a * 2 = 4 + a * 2 + 2 by omega]
    simp [Nat.factorial]
    rw [←mul_assoc, mul_comm]
    refine Nat.mul_le_mul_right (4 + a * 2)! ?_
    ring_nf
    omega

-- Assumming a ≤ b without losing generality.
lemma lemma1 {a b : ℕ} (hab' : a ≤ b) :
    a ! + b ! = (a + b) ! → (a, b) = (1, 1) :=
by
  intro H
  by_cases a0 : a = 0
  . subst a0
    simp at *
  . have bdvdab : b ! ∣ (a + b) ! := by
      apply factorial_dvd_factorial
      omega
    have advdb : a ! ∣ b ! := by
      exact factorial_dvd_factorial hab'
    have bdvda : b ! ∣ a ! := by
      rw [←H] at bdvdab
      exact Nat.dvd_add_self_right.mp bdvdab
    have : a ! = b ! := by
      exact Nat.dvd_antisymm advdb bdvda
    have : a = b := by
      apply my_factorial_inj
      . omega
      . omega
      . assumption
    subst this
    simp at *
    ring_nf at H
    by_cases h : a ≥ 2
    . have := @lemma2 (a - 2)
      rw [Nat.sub_add_cancel] at this
      omega
      omega
    interval_cases a
    . simp at *
    . simp at *

/- \section*{Exercise 4 - 241044}

Determine all pairs \((a ; b)\) of natural numbers for which \(a! + b! = (a + b)!\) holds! Hint: For every natural number \(n \geq 1\), \(n!\) is defined as the product of all natural numbers \(k\) such that \(1 \leq k \leq n\); furthermore, \(0! = 1\) is defined. -/
theorem number_theory_189785 {a b : ℕ} :
    a ! + b ! = (a + b) ! ↔ (a, b) = (1, 1) :=
by
  constructor <;> intro H
  swap
  . rcases H
    simp
  by_cases h : a ≤ b
  . apply lemma1
    <;> assumption
  . simp at h
    have : (b, a) = (1,1) := by
      apply lemma1
      omega
      ring_nf at H ⊢
      assumption
    rcases this
    simp
