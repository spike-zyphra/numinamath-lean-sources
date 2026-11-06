import Mathlib

theorem inequalities_6660 : Set.ncard {x : ℤ | 777 > 9 * x + 25 ∧ 9 * x + 25 > -29} = 89 := by 
  have h1 : {x : ℤ | 777 > 9 * x + 25 ∧ 9 * x + 25 > -29} = Set.Ioo (-6) 84 := by
    ext x
    simp
    constructor
    · -- Assume 777 > 9 * x + 25 ∧ 9 * x + 25 > -29 
      rintro ⟨h₁, h₂⟩
      constructor
      · -- Show that -6 < x 
        linarith 
      · -- Show that x < 84 
        linarith 
    · -- Assume x ∈ Set.Ioo (-6) 84 
      rintro ⟨h₁, h₂⟩
      constructor
      · -- Show that 777 > 9 * x + 25 
        linarith 
      · -- Show that 9 * x + 25 > -29 
        linarith 
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide