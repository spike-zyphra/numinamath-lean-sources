import Mathlib

theorem algebra_20036 : Set.ncard {x : ℤ | abs (x + 4) < 9} = 17 := by
  have h1 : {x : ℤ | abs (x + 4) < 9} = Set.Ioo (-13) 5 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Ioo]
    constructor
    · -- First implication: abs (x + 4) < 9 → -13 < x < 5
      intro h
      rw [abs_lt] at h
      constructor <;> linarith
    · -- Second implication: -13 < x < 5 → abs (x + 4) < 9
      rintro ⟨h1, h2⟩
      rw [abs_lt]
      constructor <;> linarith
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide