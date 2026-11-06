import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_60885 (f : ℝ → ℝ × ℝ)
  (hf : f = λ t => (4.0 * t ^ 2 - 9.0, 2.0 * t - 5.0)) :
  IsLeast {t | f t = (4.0 * t ^ 2 - 9.0, 0)} 2.5 := by
  constructor
  · -- Show that 2.5 is indeed in the set
    rw [Set.mem_setOf_eq]
    rw [hf]
    simp
    all_goals norm_num
    all_goals norm_num
  · -- Show that 2.5 is the least element in the set
    intro t ht
    rw [Set.mem_setOf_eq] at ht
    rw [hf] at ht
    simp at ht 
    norm_num at ht 
    have ht_eq : (t : ℝ) = 2.5 := by
      norm_num at ht 
      linarith 
    rw [ht_eq]
    all_goals norm_num