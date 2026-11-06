import Mathlib

theorem algebra_10299 :
    Set.ncard {n : ℕ | 0 < n ∧ 200 < n^2 ∧ n^2 < 900} = 15 := by
  have h1 : {n : ℕ | 0 < n ∧ 200 < n^2 ∧ n^2 < 900} = Set.Icc 15 29 := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have h4 : n ≥ 15 := by
        nlinarith
      have h5 : n ≤ 29 := by
        nlinarith
      constructor <;> omega
    · rintro ⟨h1, h2⟩
      constructor
      · omega
      constructor
      · nlinarith
      · nlinarith
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Finset.Icc]
  <;> native_decide