import Mathlib

open Real

theorem number_theory_10700 : ∑ x in (Finset.Icc 1 24).filter (fun y => y < 24 ∧ Nat.Coprime y 24), cos ((x * π) / 24) = 0 := by
  have h1 : (Finset.Icc 1 24).filter (fun y => y < 24 ∧ Nat.Coprime y 24) = {1, 5, 7, 11, 13, 17, 19, 23} := by 
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · -- Assume n in LHS, need prove n in RHS.
      intro h 
      rcases h with ⟨⟨hn1, hn2⟩, ⟨hn3, hn4⟩⟩
      have h2 : n ≤ 23 := by omega 
      interval_cases n <;> norm_num at *
    · -- Assume n in RHS, prove n in LHS.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Show that 1 in filter.
        simp [Nat.Coprime]
      · -- Show that 5 in filter.
        simp [Nat.Coprime]
      · -- Show that 7 in filter.
        simp [Nat.Coprime]
      · -- Show that 11 in filter.
        simp [Nat.Coprime]
      · -- Show that 13 in filter.
        simp [Nat.Coprime]
      · -- Show that 17 in filter.
        simp [Nat.Coprime]
      · -- Show that 19 in filter.
        simp [Nat.Coprime]
      · -- Show that 23 in filter.
        simp [Nat.Coprime]
  rw [h1]
  have h2 : cos ( (1 * π) / 24 ) + cos ( (5 * π) / 24 ) + cos ( (7 * π) / 24 ) + cos ( (11 * π) / 24 ) + cos ( (13 * π) / 24 ) + cos ( (17 * π) / 24 ) + cos ( (19 * π) / 24 ) + cos ( (23 * π) / 24 ) = 0 := by
    have h1 : cos ( (1 * π) / 24 ) + cos ( (23 * π) / 24 ) = 0 := by 
      have h2 : cos ( (23 * π) / 24 ) = -cos ( (1 * π) / 24 ) := by 
        have h3 : (23 * π) / 24 = π - ( (1 * π) / 24 ) := by 
          ring
        rw [h3]
        rw [cos_pi_sub]
      rw [h2]
      all_goals ring
    have h2 : cos ( (5 * π) / 24 ) + cos ( (19 * π) / 24 ) = 0 := by 
      have h3 : cos ( (19 * π) / 24 ) = -cos ( (5 * π) / 24 ) := by 
        have h4 : (19 * π) / 24 = π - ( (5 * π) / 24 ) := by
          ring 
        rw [h4]
        rw [cos_pi_sub]
      rw [h3]
      all_goals ring
    have h3 : cos ( (7 * π) / 24 ) + cos ( (17 * π) / 24 ) = 0 := by
      have h4 : cos ( (17 * π) / 24 ) = -cos ( (7 * π) / 24 ) := by 
        have h5 : (17 * π) / 24 = π - ( (7 * π) / 24 ) := by 
          ring 
        rw [h5]
        rw [cos_pi_sub]
      rw [h4]
      all_goals ring
    have h4 : cos ( (11 * π) / 24 ) + cos ( (13 * π) / 24 ) = 0 := by 
      have h5 : cos ( (13 * π) / 24 ) = -cos ( (11 * π) / 24 ) := by 
        have h6 : (13 * π) / 24 = π - ( (11 * π) / 24 ) := by 
          ring 
        rw [h6]
        rw [cos_pi_sub]
      rw [h5]
      all_goals ring
    linarith [h1, h2, h3, h4]
  have eq1 : ∑ x in ({1, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ), cos ((x * π) / 24) = 
      cos ( (1 * π) / 24 ) + cos ( (5 * π) / 24 ) + cos ( (7 * π) / 24 ) + cos ( (11 * π) / 24 ) + cos ( (13 * π) / 24 ) + cos ( (17 * π) / 24 ) + cos ( (19 * π) / 24 ) + cos ( (23 * π) / 24 ) := by 
    norm_num [Finset.sum_insert, Finset.sum_singleton]
    <;> ring
  rw [eq1]
  linarith [h2]