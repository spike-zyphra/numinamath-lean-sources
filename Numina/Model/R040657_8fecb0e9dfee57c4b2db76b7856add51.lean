import Mathlib

open Real Set
open scoped BigOperators

theorem number_theory_171787 :
  ∑ x in (Finset.Ico 1 24).filter (fun y => Nat.Coprime y 24), cos (x * π / 24) = 0 := by 
  have h1 : (Finset.Ico 1 24).filter (fun y => Nat.Coprime y 24) = {1, 5, 7, 11, 13, 17, 19, 23} := by
    ext n
    simp [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      rcases h with ⟨⟨hn1, hn2⟩, hn3⟩
      interval_cases n <;> norm_num at hn3 ⊢
    · intro h
      rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        native_decide
  rw [h1]
  have h3 : cos (23 * π / 24) = -cos (1 * π / 24) := by
    have h4 : 23 * π / 24 = π - (π / 24) := by 
      linarith [Real.pi_pos]
    rw [h4]
    have h6 : cos (π - (π / 24)) = -cos (π / 24) := by 
      rw [cos_pi_sub]
    have h7 : (1 * π / 24 : ℝ) = π / 24 := by 
      ring_nf
    have h8 : -cos (π / 24) = -cos (1 * π / 24) := by 
      rw [show (1 * π / 24 : ℝ) = π / 24 by ring_nf]
    have h9 : cos (π - (π / 24)) = -cos (1 * π / 24) := by 
      linarith [h6, h7, h8]
    exact_mod_cast h9
  have h3' : cos (19 * π / 24) = -cos (5 * π / 24) := by 
    have h4 : 19 * π / 24 = π - (5 * π / 24) := by 
      linarith [Real.pi_pos]
    rw [h4]
    have h6 : cos (π - (5 * π / 24)) = -cos (5 * π / 24) := by 
      rw [cos_pi_sub]
    linarith [h6]
  have h3'' : cos (17 * π / 24) = -cos (7 * π / 24) := by 
    have h4 : 17 * π / 24 = π - (7 * π / 24) := by 
      linarith [Real.pi_pos]
    rw [h4]
    have h6 : cos (π - (7 * π / 24)) = -cos (7 * π / 24) := by 
      rw [cos_pi_sub]
    linarith [h6]
  have h3''' : cos (13 * π / 24) = -cos (11 * π / 24) := by 
    have h4 : 13 * π / 24 = π - (11 * π / 24) := by 
      linarith [Real.pi_pos]
    rw [h4]
    have h6 : cos (π - (11 * π / 24)) = -cos (11 * π / 24) := by 
      rw [cos_pi_sub]
    linarith [h6]
  have h11 : cos (1 * π / 24) + cos (5 * π / 24) + cos (7 * π / 24) + cos (11 * π / 24) + cos (13 * π / 24) + cos (17 * π / 24) + cos (19 * π / 24) + cos (23 * π / 24) = 0 := by 
    have eq1 : cos (23 * π / 24) = -cos (1 * π / 24) := h3
    have eq2 : cos (19 * π / 24) = -cos (5 * π / 24) := h3'
    have eq3 : cos (17 * π / 24) = -cos (7 * π / 24) := h3''
    have eq4 : cos (13 * π / 24) = -cos (11 * π / 24) := h3'''
    linarith [eq1, eq2, eq3, eq4]
  norm_num [Finset.sum_insert, Finset.sum_singleton, h11] at *
  all_goals
    try { linarith [Real.pi_pos] }