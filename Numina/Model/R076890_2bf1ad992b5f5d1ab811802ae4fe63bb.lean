import Mathlib

theorem inequalities_6803 :
    Set.ncard {x : ℤ | x < 0 ∧ -97 ≤ 7 * x + 3 ∧ 7 * x + 3 ≤ 32} = 14 := by
  have h1 : {x : ℤ | x < 0 ∧ -97 ≤ 7 * x + 3 ∧ 7 * x + 3 ≤ 32} = Set.Icc (-14) (-1) := by 
    ext x 
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor 
    · -- Assume x satisfies all the conditions, we need to show it's in the interval [-14, -1]
      rintro ⟨h1, h2, h3⟩ 
      omega 
    · -- Assume x is in the interval [-14, -1], we need to show it satisfies all the conditions 
      rintro ⟨h1, h2⟩ 
      constructor 
      · -- Show x < 0 
        omega 
      constructor 
      · -- Show -97 ≤ 7 * x + 3 
        omega 
      · -- Show 7 * x + 3 ≤ 32 
        omega 
  rw [h1] 
  rw [Set.ncard_eq_toFinset_card'] 
  simp [Int.card_Icc]
  <;> try omega