import Mathlib
open Mathlib

theorem number_theory_4096 : IsLeast {z : ℕ | ∃a b : ℕ, 0 < a ∧ 0 < b ∧ ⌊(3 * a : ℝ) / (8 * b : ℝ)⌋ = 7 ∧ z = a + b} 20 := by 
  constructor
  · -- Show that 20 is in the set.
    use 19, 1
    norm_num [Int.floor_eq_iff]
    all_goals norm_num

  · -- Show that no smaller element is in the set.
    intro z hz
    rcases hz with ⟨a, b, ha, hb, h_floor, hz⟩
    
    by_contra h
    push_neg at h 
    have h1 : z < 20 := by 
      omega
    have h2 : a + b < 20 := by
      omega -- from z = a + b and h1
    have h3 : ⌊(3 * a : ℝ) / (8 * b : ℝ)⌋ = 7 := h_floor
    have h4 : a < 20 := by 
      omega
    have h5 : b < 20 := by 
      omega 
    interval_cases a <;> interval_cases b
    <;> norm_num at h3 hz <;> all_goals omega