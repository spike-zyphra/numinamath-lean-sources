import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_12695 {a : ℝ} (P Q : Set ℝ)
  (hP : P = {x | abs (x - 1) < 1}) (hQ : Q = {x | abs (x - a) ≤ 1})
  (hPQ : P ∩ Q ≠ ∅) :
  -1 ≤ a ∧ a ≤ 3 := by 
  -- First, prove that existence in P ∩ Q implies inequalities on a
  have h1 : ∃ x, x ∈ P ∩ Q := by 
    by_contra h
    push_neg at h
    have h2 : P ∩ Q = ∅ := by 
      ext x
      simp
      all_goals 
        aesop
    contradiction
  rcases h1 with ⟨x, hx⟩
  rw [hP] at hx 
  rw [hQ] at hx 
  simp at hx 
  have h2 : 0 < x ∧ x < 2 := by 
    constructor 
    · linarith [abs_lt.mp hx.1]
    · linarith [abs_lt.mp hx.1]
  have h3 : a - 1 ≤ x ∧ x ≤ a + 1 := by 
    constructor 
    · linarith [abs_le.mp hx.2]
    · linarith [abs_le.mp hx.2]
  constructor
  · linarith 
  · linarith