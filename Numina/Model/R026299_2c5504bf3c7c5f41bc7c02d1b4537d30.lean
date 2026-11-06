import Mathlib

theorem algebra_9709 :
  {(x, y) : ℤ × ℤ | x^2 + 2 * y^2 + 4 * x - 12 * y = 122}.ncard = 6 := by 
  have h1 : {(x, y) : ℤ × ℤ | x^2 + 2 * y^2 + 4 * x - 12 * y = 122} = {(-6, -5), (2, -5), (10, 3), (-14, 3), (2, 11), (-6, 11)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Show that eq hold means solutions
      rintro h
      have eq1 : (x + 2) ^ 2 + 2 * (y - 3 : ℤ) ^ 2 = 144 := by
        nlinarith
      have h3 : y ≥ -5 := by
        by_contra h
        push_neg at h
        have h4 : (y - 3 : ℤ) ≤ -6 := by omega
        have h5 : (y - 3 : ℤ) ^ 2 ≥ 36 := by
          nlinarith [sq_nonneg ((y - 3 : ℤ) + 6 : ℤ)]
        nlinarith [h5, sq_nonneg ((x + 2) : ℤ)]
      have h4 : y ≤ 11 := by
        by_contra h
        push_neg at h
        have h5 : (y - 3 : ℤ) ≥ 8 := by omega
        have h6 : (y - 3 : ℤ) ^ 2 ≥ 64 := by
          nlinarith [sq_nonneg ((y - 3 : ℤ) - 8 : ℤ)]
        nlinarith [h6, sq_nonneg ((x + 2) : ℤ)]
      interval_cases y <;> norm_num at eq1 <;> try { 
        have h6 : (x ) ≤ 14 := by
          nlinarith
        have h7 : x ≥ -16 := by
          nlinarith
        interval_cases x <;> norm_num at eq1 ⊢
        <;> tauto
      }
    · -- Show that the pairs in the finite set are solutions
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide