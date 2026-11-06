import Mathlib

theorem algebra_103953 (x y : ℕ) : x^2 = y^2 + 7 * y + 6 ↔ (x, y) = (6, 3) := by 
  constructor
  · -- Assume x^2 = y^2 + 7 * y + 6, show (x, y) = (6, 3)
    rintro h
    have h1 : x ^ 2 = y ^ 2 + 7 * y + 6 := h
    have h2 : x ≤ y + 3 := by 
      nlinarith [sq_nonneg (x - (y + 3)), sq_nonneg (y - 3), sq_nonneg (x - 6), sq_nonneg (y - 3)]
    have h3 : y ≤ 6 := by
      nlinarith [sq_nonneg (y - 3), sq_nonneg (x - 6), h2, h1]
    have h4 : y ≤ 6 := by 
      nlinarith [sq_nonneg (y - 3), sq_nonneg (x - 6), h2, h1]
    have h5 : x ≤ 9 := by
      nlinarith [h4, h1]
    interval_cases y <;> interval_cases x
      <;> norm_num at h1
      <;> simp [Prod.ext_iff]
      <;> all_goals tauto

  · -- Assume (x, y) = (6, 3), show x^2 = y^2 + 7 * y + 6
    rintro ⟨rfl, rfl⟩
    norm_num