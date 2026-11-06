import Mathlib

theorem inequalities_5074 : {x : ℤ | -23 ≤ 4 * x + 3 ∧ 4 * x + 3 ≤ 29}.encard = 13 := by 
  have h : {x : ℤ | -23 ≤ 4 * x + 3 ∧ 4 * x + 3 ≤ 29} = Set.Icc (-6 : ℤ) 6 := by
    ext x 
    simp 
    constructor 
    · rintro ⟨h1, h2⟩ 
      omega 
    · rintro ⟨h1, h2⟩
      omega 
  rw [h]
  rw [Set.encard]
  simp
  <;> rfl
  all_goals try { norm_num }
  all_goals try { tauto }