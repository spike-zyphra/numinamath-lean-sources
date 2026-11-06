import Mathlib

theorem number_theory_227837_solution_set :
    { (x, y) : ℤ × ℤ | x ≥ 0 ∧ y ≥ 0 ∧ y^3 = x^3 + 8 * x^2 - 6 * x + 8 } = 
    {(0, 2), (9, 11)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x, y) is a solution, prove that (x, y) = (0, 2) or (9, 11)
    rintro ⟨hx, hy, h_eq⟩
    have h1 : y^3 = x^3 + 8 * x^2 - 6 * x + 8 := h_eq
    have h2 : y > x := by
      nlinarith [sq_nonneg (y - x), sq_nonneg (y + x), sq_nonneg (x - 4), sq_nonneg (y - 2), sq_nonneg (x - 9), sq_nonneg (y - 11), sq_nonneg (y ^ 2 - x ^ 2), sq_nonneg (y * x - 2 * x)]
    have h3 : y ≤ x + 2 := by
      nlinarith [sq_nonneg (y - (x + 2)), sq_nonneg ((x + 2) ^ 2 - x ^ 2), sq_nonneg ((x + 2) ^ 3 - x ^ 3), sq_nonneg (x - y), sq_nonneg (x + 2 - y), sq_nonneg (x - 9), sq_nonneg (y - 11)]
    have h4 : y = x + 1 ∨ y = x + 2 := by 
      omega 
    rcases h4 with h4 | h4
    · -- y = x + 1
      have h5 : y = x + 1 := h4
      rw [h5] at h_eq
      have h5 : 5 * x^2 - 9 * x + 7 = 0 := by
        nlinarith 
      nlinarith [sq_nonneg (x - 5), sq_nonneg (x * 5 -45), sq_nonneg (x - 1)]
    · -- y = x + 2
      have h5 : y = x + 2 := h4
      rw [h5] at h_eq
      have h6 : 2 * x * (x - 9) = 0 := by
        nlinarith 
      cases' (mul_eq_zero.mp h6) with h7 h8
      · -- 2 * x = 0
        have h6 : x = 0 := by linarith
        have h7 : y = 2 := by 
          nlinarith [h6, h5]
        omega 
      · -- x - 9 = 0
        have h8 : x = 9 := by linarith 
        have h9 : y = 11 := by 
          nlinarith [h8, h5]
        omega 
  · -- Show that (0, 2) and (9, 11) are solutions
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Check (0, 2)
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Check (9, 11)
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num