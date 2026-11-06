import Mathlib

theorem number_theory_129208 :
    {(x, y) : ℤ × ℤ | x > 0 ∧ y > 0 ∧ x ^ 3 - y ^ 3 = x * y + 41} = {(5, 4)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume h : (x,y) is a positive integer solution
    rintro ⟨hx, hy, heq⟩
    have h1 : x > y := by nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 5), sq_nonneg (y - 4)]
    have h3 : x ≤ 10 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 5), sq_nonneg (y - 4), mul_pos hx hy, sq_nonneg (x - 10), sq_nonneg (y - 9)]
    have h4 : y ≤ 10 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 5), sq_nonneg (y - 4), mul_pos hx hy, sq_nonneg (x - 10), sq_nonneg (y - 9)]
    interval_cases x <;> interval_cases y
    <;> omega
  · -- Assume (5, 4)
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num