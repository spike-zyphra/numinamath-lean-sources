import Mathlib

theorem algebra_4798 :
    IsLeast {z : ℤ | ∃ x y : ℤ, x > 0 ∧ y > 0 ∧ x + 2 * x * y - 4 * y = 11 ∧ z = 3 * y - x} (-2) := by 
  constructor 
  · -- Show -2 is indeed in the set
    use 5, 1
    norm_num
  · -- Show -2 is minimal
    intro z h
    rcases h with ⟨x, y, hx, hy, heq, hz⟩
    by_contra h
    push_neg at h 
    -- So h : z < -2
    have h1 : x > 3 * y + 2 := by 
      nlinarith [hz, h]
    have h2 : x + 2 * x * y - 4 * y = 11 := heq
    -- bound variables
    have h3 : y ≤ 4 := by
      nlinarith [sq_nonneg (x - 5 : ℤ), sq_nonneg (y - 1 : ℤ), sq_nonneg (y - 4 : ℤ), mul_pos hx hy]
    have h4 : y ≥ 1 := by
      linarith 
    have h5 : x ≤ 11 := by
      nlinarith [sq_nonneg (y - 1 : ℤ), sq_nonneg (x - 1 : ℤ), sq_nonneg (x - 5 : ℤ), sq_nonneg (y - 4 : ℤ), mul_pos hx hy, heq]
    interval_cases y <;> interval_cases x 
    <;> omega