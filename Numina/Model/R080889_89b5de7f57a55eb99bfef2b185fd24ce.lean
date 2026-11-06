import Mathlib

theorem inequalities_6848 : {z : ℤ | 662 > 7 * z + 18 ∧ -31 < 7 * z + 18}.encard = 98 := by
  have h1 : {z : ℤ | 662 > 7 * z + 18 ∧ -31 < 7 * z + 18} = Set.Icc (-6) 91 := by 
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Show that if $z$ satisfies the inequalities, $z \in Set.Icc (-6) 91$.
      rintro ⟨h1, h2⟩
      omega
    · -- Show that if $z \in Set.Icc (-6) 91$, $z$ satisfies the inequalities.
      rintro ⟨h1, h2⟩
      constructor
      · -- Show 662 > 7 * z + 18
        omega
      · -- Show -31 < 7 * z + 18
        omega
  rw [h1]
  rw [Set.encard]
  simp [Int.card_Icc]
  <;> try native_decide