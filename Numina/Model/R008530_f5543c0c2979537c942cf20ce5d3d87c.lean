import Mathlib

theorem algebra_15630 : {x : ℝ | 5 / 24 + abs (x - 11 / 48) < 5 / 16} = Set.Ioo (1 / 8) (1 / 3) := by 
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · -- First, we prove that if 5/24 + abs (x - 11/48) < 5/16, then 1/8 < x < 1/3.
    intro h
    have h1 : abs (x - 11 / 48) < 5 / 48 := by linarith
    have h2 : -(5 / 48) < x - 11 / 48 := by
      linarith [abs_lt.mp h1]
    have h3 : x - 11 / 48 < 5 / 48 := by
      linarith [abs_lt.mp h1]
    constructor
    · -- Proof that x > 1/8
      linarith
    · -- Proof that x < 1/3
      linarith
  · -- Now prove the reverse: if 1/8 < x < 1/3, then 5/24 + abs (x - 11/48) < 5/16.
    rintro ⟨h1, h2⟩
    have h3 : abs (x - 11 / 48) < 5 / 48 := by 
      rw [abs_lt]
      constructor 
      all_goals 
      linarith 
    linarith [abs_lt.mp h3]