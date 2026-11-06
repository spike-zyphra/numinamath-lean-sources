import Mathlib

theorem inequalities_5840 : Set.ncard {x : ℤ | -9 ≤ (7 * x + 5) / 4 ∧ (7 * x + 5) / 4 ≤ 17} = 15 := by 
  have h1 : {x : ℤ | -9 ≤ (7 * x + 5) / 4 ∧ (7 * x + 5) / 4 ≤ 17} = Set.Icc (-5) 9 := by 
    ext x 
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Assume the inequality holds, prove x ∈ Icc (-5) 9
      intro h 
      rcases h with ⟨h1, h2⟩
      have h3 : -41 ≤ 7 * x := by 
        omega 
      have h4 : 7 * x ≤ 63 := by 
        omega 
      omega 
    · -- Assume x ∈ Icc (-5) 9, prove inequalities 
      rintro ⟨h1, h2⟩
      constructor 
      · -- Show -9 ≤ (7 * x + 5) / 4
        omega 
      · -- Show (7 * x + 5) / 4 ≤ 17
        omega 
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide