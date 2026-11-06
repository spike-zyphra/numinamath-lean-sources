import Mathlib

theorem algebra_260022 :
  {x : ℝ | x ≠ 7 ∧ x ≠ 8 ∧ (x + 7)/(x - 8) - 6 = (5 * x - 55)/(7 - x)} = {11} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, prove that if x is in the set, then x = 11
    rintro ⟨hx1, hx2, heq⟩
    have h1 : x - 8 ≠ 0 := by 
      intro h
      apply hx2
      linarith
    have h2 : (7 - x) ≠ 0 := by 
      intro h
      apply hx1
      linarith
    field_simp [(show x - 8 ≠ 0 by assumption), (show (7 - x) ≠ 0 by assumption)] at heq
    have h_eq : x = 11 := by
      nlinarith
    exact h_eq
  · -- Now prove the reverse: if x = 11, then it is in the set
    intro h_eq 
    rw [h_eq]
    constructor 
    · -- Show that 11 ≠ 7
      norm_num 
    constructor
    · -- Show that 11 ≠ 8
      norm_num
    · -- Check the equation 
      norm_num