import Mathlib

theorem algebra_207138 :
    Set.ncard {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = 6 * p.1 + 2 * p.2 + 15} = 12 := by
  have h1 : {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = 6 * p.1 + 2 * p.2 + 15} = { 
    (3, 6), (3, -4), (8, 1), (-2, 1), (6, 5), (6, -3), (0, 5), (0, -3), (7, 4), (7, -2), (-1, 4), (-1, -2)
  } := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume h: x^2 + y^2 = 6*x + 2*y + 15, derive h2
      rintro h
      have h_eq : (x - 3) ^ 2 + (y - 1) ^ 2 = 25 := by
        nlinarith
      have h2 : x ≤ 8 := by
        nlinarith [sq_nonneg (x - 3 : ℤ), sq_nonneg (y - 1 : ℤ)]
      have h3 : x ≥ -2 := by
        nlinarith [sq_nonneg (x - 3 : ℤ), sq_nonneg (y - 1 : ℤ)]
      have h4 : y ≤ 6 := by
        nlinarith [sq_nonneg (x - 3 : ℤ), sq_nonneg (y - 1 : ℤ)]
      have h5 : y ≥ -4 := by
        nlinarith [sq_nonneg (x - 3 : ℤ), sq_nonneg (y - 1 : ℤ)]
      interval_cases x <;> interval_cases y
      <;> norm_num at h_eq h ⊢
      <;> tauto
    · -- Show that each of the pairs in the right side set is in the left side
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Verify (3, 6) is a solution
        norm_num
      · -- Verify (3, -4) is a solution
        norm_num
      · -- Verify (8, 1) is a solution
        norm_num
      · -- Verify (-2, 1) is a solution
        norm_num
      · -- Verify (6, 5) is a solution
        norm_num
      · -- Verify (6, -3) is a solution
        norm_num
      · -- Verify (0, 5) is a solution
        norm_num
      · -- Verify (0, -3) is a solution
        norm_num
      · -- Verify (7, 4) is a solution
        norm_num
      · -- Verify (7, -2) is a solution
        norm_num
      · -- Verify (-1, 4) is a solution
        norm_num
      · -- Verify (-1, -2) is a solution
        norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }