import Mathlib

theorem algebra_22154 : {(x, y) : ℤ × ℤ | x^2 + y^2 = 25}.ncard = 12 := by 
  have h1 : {(x, y) : ℤ × ℤ | x^2 + y^2 = 25} = {(-3, -4), (-3, 4), (-4, -3), (-4, 3), (3, -4), (3, 4), (4, -3), (4, 3), (-5, 0), (5, 0), (0, -5), (0, 5)} := by
    ext ⟨x, y⟩
    simp 
    constructor
    · -- Assume (x, y) is in the left side.
      intro h
      have h_eq : x^2 + y^2 = 25 := h 
      have h3 : x ≤ 5 := by nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ)]
      have h4 : x ≥ -5 := by nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ)]
      have h5 : y ≤ 5 := by nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ)]
      have h6 : y ≥ -5 := by nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ)]
      interval_cases x <;> interval_cases y 
      <;> norm_num at h_eq ⊢ 
    · -- Assume (x, y) is in the right side.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · norm_num 
      · norm_num 
      · norm_num 
      · norm_num 
      · norm_num 
      · norm_num 
      · norm_num 
      · norm_num 
      · norm_num 
      · norm_num 
      · norm_num 
      · norm_num 
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide