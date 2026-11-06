import Mathlib

theorem algebra_179681 :
    {z : ℝ | ∃ x y, 0 < x ∧ 0 < y ∧ 1 / (1 + x + x ^ 2) + 1 / (1 + y + y ^ 2) + 1 / (1 + x + y) = 1 ∧ z = x * y} = {1} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume z in left side
    rintro ⟨x, y, hx, hy, heq, hz⟩
    have h1 : 0 < x * y := mul_pos hx hy
    have h2 : (1 + x + x ^ 2) > 0 := by
      nlinarith [sq_nonneg (x + 1 / 2), sq_pos_of_pos hx]
    have h3 : (1 + y + y ^ 2) > 0 := by
      nlinarith [sq_nonneg (y + 1 / 2), sq_pos_of_pos hy]
    have h4 : (1 + x + y) > 0 := by
      nlinarith [show 0 < x from hx, show 0 < y from hy]
    have heq' : (1 + y + y^2) * (1 + x + y) + (1 + x + x^2) * (1 + x + y) + (1 + x + x^2) * (1 + y + y^2) = (1 + x + x^2) * (1 + y + y^2) * (1 + x + y) := by
      have h5 : (1 + x + x ^ 2) > 0 := h2
      have h6 : (1 + y + y ^ 2) > 0 := h3
      have h7 : (1 + x + y) > 0 := h4
      field_simp at heq ⊢
      nlinarith [mul_pos hx hy, mul_pos hx (show 0 < y ^ 2 by nlinarith), mul_pos (show 0 < x ^ 2 by nlinarith) hy]
    have h5 : (x * y - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x - y), sq_nonneg (x * y - 1), mul_pos hx hy, mul_pos hx (show 0 < y ^ 2 by nlinarith), mul_pos (show 0 < x ^ 2 by nlinarith) hy, sq_nonneg (x * y), sq_nonneg (x + y)]
    have h6 : x * y - 1 = 0 := by
      apply pow_eq_zero 
      exact h5
    have h7 : x * y = 1 := by linarith
    linarith [hz, h7]
  · -- Assume z = 1
    intro h
    rw [h]
    use 1, 1
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    all_goals norm_num