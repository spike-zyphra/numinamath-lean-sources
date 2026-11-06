import Mathlib

theorem algebra_202422 : {(x, y) : ℤ × ℤ | x^2 + y^2 = 6 * x + 2 * y + 15}.encard = 12 := by 
  have h1 : {(x, y) : ℤ × ℤ | x^2 + y^2 = 6 * x + 2 * y + 15} = {(-2, 1), (8, 1), (3, 6), (3, -4), (6, 5), (6, -3), (0, 5), (0, -3), (7, 4), (7, -2), (-1, 4), (-1, -2)} := by 
    ext ⟨x, y⟩
    simp 
    constructor
    · -- Assume (x, y) satisfies x^2 + y^2 = 6 * x + 2 * y + 15, prove (x, y) ∈ {(-2, 1), (8, 1), (3, 6), (3, -4), (6, 5), (6, -3), (0, 5), (0, -3), (7, 4), (7, -2), (-1, 4), (-1, -2)}
      rintro H 
      have h1 : (x - 3) ^ 2 + (y - 1) ^ 2 = 25 := by 
        nlinarith
      have h2 : x ≤ 8 := by nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 1)]
      have h3 : x ≥ -2 := by nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 1)]
      have h4 : y ≤ 6 := by nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 1)]
      have h5 : y ≥ -4 := by nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 1)]
      interval_cases x <;> interval_cases y 
      <;> norm_num at h1 ⊢ 
      <;> tauto
    · -- Assume (x, y) ∈ {(-2, 1), (8, 1), (3, 6), (3, -4), (6, 5), (6, -3), (0, 5), (0, -3), (7, 4), (7, -2), (-1, 4), (-1, -2)}, prove x^2 + y^2 = 6 * x + 2 * y + 15 
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals 
        norm_num 
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }
  <;> try { tauto }
  <;> try { omega }
  <;> try { linarith }
  <;> try { norm_num }