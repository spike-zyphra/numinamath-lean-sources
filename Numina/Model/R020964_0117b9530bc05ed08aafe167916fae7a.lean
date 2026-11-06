import Mathlib

theorem algebra_135077 :
    {(x, y) : ℤ × ℤ | y^4 - 8 * y^2 + 7 = 8 * x^2 - 2 * x^2 * y^2 - x^4}.encard = 4 := by
  have h1 : {(x, y) : ℤ × ℤ | y^4 - 8 * y^2 + 7 = 8 * x^2 - 2 * x^2 * y^2 - x^4} = {(-1, 0), (0, -1), (0, 1), (1, 0)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume (x, y) is a solution
      rintro H
      have h2 : x^4 + y^4 + 2 * x^2 * y^2 = 8 * x^2 + 8 * y^2 - 7 := by
        linarith
      have h3 : (x^2 + y^2) ^ 2 = 8 * (x^2 + y^2) - 7 := by
        nlinarith
      have h4 : (x^2 + y^2) ^ 2 - 8 * (x^2 + y^2) + 7 = 0 := by
        nlinarith
      have h5 : (x^2 + y^2 - 1) * (x^2 + y^2 - 7) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h5) with h6 h7
      · -- Case 1: x^2 + y^2 = 1
        have h8 : x^2 + y^2 = 1 := by
          nlinarith
        have h9 : x ≥ -1 := by
          nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ), sq_nonneg (x + 1 : ℤ), sq_nonneg (y + 1 : ℤ), h8]
        have h10 : x ≤ 1 := by
          nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ), sq_nonneg (x - 1 : ℤ), sq_nonneg (y - 1 : ℤ), h8]
        have h11 : y ≥ -1 := by
          nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ), sq_nonneg (y + 1 : ℤ), sq_nonneg (x + 1 : ℤ), h8]
        have h12 : y ≤ 1 := by
          nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ), sq_nonneg (y - 1 : ℤ), sq_nonneg (x - 1 : ℤ), h8]
        interval_cases x <;> interval_cases y
          <;> norm_num at h8
          <;> tauto
      · -- Case 2: x^2 + y^2 = 7
        have h8 : x^2 + y^2 = 7 := by
          nlinarith
        have h9 : x ≥ -2 := by
          nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ), sq_nonneg (x + 2 : ℤ), sq_nonneg (y + 2 : ℤ), h8]
        have h10 : x ≤ 2 := by
          nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ), sq_nonneg (x - 2 : ℤ), sq_nonneg (y - 2 : ℤ), h8]
        have h11 : y ≥ -2 := by
          nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ), sq_nonneg (y + 2 : ℤ), sq_nonneg (x + 2 : ℤ), h8]
        have h12 : y ≤ 2 := by
          nlinarith [sq_nonneg (x : ℤ), sq_nonneg (y : ℤ), sq_nonneg (y - 2 : ℤ), sq_nonneg (x - 2 : ℤ), h8]
        interval_cases x <;> interval_cases y
          <;> omega
    · -- Show that these four solutions are actually solutions.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try {
      native_decide
  }