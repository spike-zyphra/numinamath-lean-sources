import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_326600 (a : ℝ) (p q : ℝ → Prop)
  (hp : p = λ x => abs (4 * x - 3) < 1)
  (hq : q = λ x => x ^ 2 - (2 * a + 1) * x + a * (a + 1) ≤ 0)
  (hnp : ∀ x, q x → p x)
  (hns : ∃ x, p x ∧ ¬q x) :
  0 ≤ a ∧ a ≤ 1 / 2 := by

  have hp1 : ∀ x, p x ↔ abs (4 * x - 3) < 1 := by
    intro x
    simpa [hp]

  have hp2 : ∀ x, q x ↔ x ^ 2 - (2 * a + 1) * x + a * (a + 1) ≤ 0 := by
    intro x
    simpa [hq]

  have hq_a : q a := by 
    rw [hp2]
    nlinarith
  have hq_a1 : q (a + 1) := by
    rw [hp2]
    nlinarith

  have hp_a : p a := hnp a hq_a
  have hp_a1 : p (a + 1) := hnp (a + 1) hq_a1

  have hp_a' : abs (4 * a - 3) < 1 := by
    rw [hp1] at hp_a
    exact hp_a

  have hp_a1' : abs (4 * (a + 1) - 3) < 1 := by
    rw [hp1] at hp_a1
    exact hp_a1
  have h6 : 0.5 < a := by
    have h11 : abs (4 * a - 3) < 1 := hp_a'
    have h7 : -1 < 4 * a - 3 := by 
      linarith [abs_lt.mp h11]
    have h8 : 4 * a - 3 < 1 := by
      linarith [abs_lt.mp h11]
    nlinarith
  have h7 : a < (0 : ℝ) := by
    have h11 : abs (4 * (a + 1) - 3) < 1 := hp_a1'
    have h7 : -1 < 4 * (a + 1) - 3 := by 
      linarith [abs_lt.mp h11]
    have h8 : 4 * (a + 1) - 3 < 1 := by 
      linarith [abs_lt.mp h11]
    nlinarith

  constructor 
  · -- Proof that 0 ≤ a.
    nlinarith 
  · -- Proof that a ≤ 1/2.
    nlinarith