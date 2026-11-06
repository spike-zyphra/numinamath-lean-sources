import Mathlib

theorem algebra_325598 :
    {(x, y) : ℤ × ℤ | x^2 + x * y + 2 * y^2 = 29}.encard = 4 := by
  have h1 : {(x, y) : ℤ × ℤ | x^2 + x * y + 2 * y^2 = 29} = {(-3, 4), (-1, 4), (1, -4), (3, -4)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume (x, y) is a solution, prove it is in the right side
      rintro H
      have h2 : y ≥ -4 := by
        nlinarith [sq_nonneg (2 * x + y), sq_nonneg (y + 4), sq_nonneg (y - 4)]
      have h3 : y ≤ 4 := by
        nlinarith [sq_nonneg (2 * x + y), sq_nonneg (y - 4), sq_nonneg (y + 4)]
      interval_cases y <;> try { 
        have h4 : x ≤ 7 := by 
          nlinarith 
        have h5 : x ≥ -7 := by 
          nlinarith 
        interval_cases x <;> norm_num at H ⊢ 
        <;> tauto
      }
    · -- Show that these are solutions
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try native_decide