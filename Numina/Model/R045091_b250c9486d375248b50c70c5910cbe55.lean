import Mathlib

theorem number_theory_7786 :
  {(x, y) : ℤ × ℤ | x > 0 ∧ y > 0 ∧ x ^ 3 - y ^ 3 = x * y + 61} = {(6, 5)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x, y) is a positive integer solution, prove (x, y) = (6, 5)
    rintro ⟨hx, hy, h⟩
    have h1 : x > y := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 6), sq_nonneg (y - 5), mul_pos hx hy]
    have h2 : x ≤ 14 := by
      nlinarith [sq_nonneg (x - 6), sq_nonneg (y - 5), sq_nonneg (x - y), sq_nonneg (x + y),
        mul_pos hx hy, sq_nonneg (x ^ 2 - y ^ 2)]
    have h3 : y ≤ 14 := by
      nlinarith [sq_nonneg (x - 6), sq_nonneg (y - 5), sq_nonneg (x - y), sq_nonneg (x + y),
        mul_pos hx hy, sq_nonneg (x ^ 2 - y ^ 2)]
    interval_cases x <;> interval_cases y
    <;> norm_num at h ⊢
    <;> tauto
  · -- Show (6, 5) is a positive integer solution
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num