import Mathlib

theorem algebra_252705 :
  { (x, y) : ℤ × ℤ | x + y = x ^ 2 - x * y + y ^ 2 } =
  { (0, 0), (2, 2), (1, 0), (0, 1), (2, 1), (1, 2) } := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume x + y = x^2 - x * y + y^2, prove (x,y) from the set
    rintro h
    have h1 : x ≤ 2 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x - y)]
    have h2 : y ≤ 2 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x - y)]
    have h3 : x ≥ 0 := by
      nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x - y)]
    have h4 : y ≥ 0 := by
      nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x - y)]
    interval_cases x <;> interval_cases y <;> omega
  · -- Assume (x,y) from the set, prove x+y =x ^ 2 -x * y +y ^ 2
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- (0,0)
      norm_num
    · -- (2,2)
      norm_num
    · -- (1,0)
      norm_num
    · -- (0,1)
      norm_num
    · -- (2,1)
      norm_num
    · -- (1,2)
      norm_num