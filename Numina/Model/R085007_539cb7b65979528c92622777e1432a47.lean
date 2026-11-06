import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_15363 {f : ℝ → ℝ} (hf : f = λ x => cos (x / 2)) :
    Function.Periodic f (4 * π) := by 
  rw [hf]
  unfold Function.Periodic
  intro x
  have h1 : cos ((x + 4 * π) / 2) = cos (x / 2) := by
    have h2 : (x + 4 * π) / 2 = x / 2 + 2 * π := by
      ring
    rw [h2]
    have h3 : cos (x / 2 + 2 * π) = cos (x / 2) := by 
      rw [cos_add_two_pi]
    exact h3
  simp [h1]
  all_goals ring_nf <;> try { tauto } <;> try { linarith [pi_pos] }
  all_goals try { tauto }
  all_goals try { linarith [pi_pos] }
  all_goals try { tauto }