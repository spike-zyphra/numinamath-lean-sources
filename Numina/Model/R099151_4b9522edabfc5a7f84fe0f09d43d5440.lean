import Mathlib

theorem algebra_307276 :
    {(x, y) : ℤ × ℤ | x^2 + x * y + 2 * y^2 = 29}.ncard = 4 := by
  have h0 : {(x, y) : ℤ × ℤ | x^2 + x * y + 2 * y^2 = 29} = {(-3, 4), (-1, 4), (1, -4), (3, -4)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Forward: if (x, y) is a solution, then it is one of the four points
      rintro H
      have h8 : y ≤ 4 := by
        nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x * y), sq_nonneg (x), sq_nonneg (y), sq_nonneg (x + 2 * y), sq_nonneg (2 * x + y)]
      have h9 : y ≥ -4 := by
        nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x * y), sq_nonneg (x), sq_nonneg (y), sq_nonneg (x + 2 * y), sq_nonneg (2 * x + y)]
      interval_cases y <;> 
        try { 
          have h10 : x ≤ 20 := by nlinarith [sq_nonneg (x), sq_nonneg (x - 9), sq_nonneg (x + 9)]
          have h11 : x ≥ -20 := by nlinarith [sq_nonneg (x), sq_nonneg (x - 9), sq_nonneg (x + 9)]
          interval_cases x <;> omega
        }
      <;> omega -- This is needed to close goals when `interval_cases` yields the values
    · -- Backward: each of the four points is a solution
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check (-3, 4)
        norm_num
      · -- Check (-1, 4)
        norm_num
      · -- Check (1, -4)
        norm_num
      · -- Check (3, -4)
        norm_num
  rw [h0]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> rfl
  all_goals nlinarith