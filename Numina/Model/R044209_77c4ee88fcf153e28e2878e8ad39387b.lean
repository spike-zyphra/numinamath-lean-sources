import Mathlib

theorem algebra_284039 :
    {(x, y) : ℤ × ℤ | x ^ 2 + y ^ 2 = 2 * (x + y) + x * y}.encard = 6 := by
  have h1 : {(x, y) : ℤ × ℤ | x ^ 2 + y ^ 2 = 2 * (x + y) + x * y} = {(0, 0), (2, 0), (0, 2), (4, 2), (2, 4), (4, 4)} := by
    ext ⟨x, y⟩
    simp 
    constructor
    · -- If (x,y) is a solution, then (x,y) ∈ {(0,0),(2,0),(0,2),(4,2),(2,4),(4,4)}
      rintro H
      have h2 : x ≤ 4 := by nlinarith [sq_nonneg (x - 4 : ℤ), sq_nonneg (y), sq_nonneg (y - 4 : ℤ)]
      have h3 : x ≥ 0 := by nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y - 0 : ℤ), sq_nonneg (y - 4 : ℤ)]
      have h4 : y ≤ 4 := by nlinarith [sq_nonneg (y - 4 : ℤ), sq_nonneg (x : ℤ), sq_nonneg (x - 4 : ℤ)]
      have h5 : y ≥ 0 := by nlinarith [sq_nonneg (y : ℤ), sq_nonneg (x - 0 : ℤ), sq_nonneg (x - 4 : ℤ)]
      interval_cases x <;> interval_cases y <;> omega
    · -- If (x,y) ∈ {(0,0),(2,0),(0,2),(4,2),(2,4),(4,4)}, then (x,y) is a solution
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check (0, 0)
        norm_num
      · -- Check (2, 0)
        norm_num
      · -- Check (0, 2)
        norm_num
      · -- Check (4, 2)
        norm_num
      · -- Check (2, 4)
        norm_num
      · -- Check (4, 4)
        norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }