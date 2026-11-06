import Mathlib

theorem algebra_263798 :
    {(a, b) : ℝ × ℝ | ∃ x1 x2, x1 ≠ x2 ∧ 2 * x1 ^ 3 + a * x1 - 12 = 0 ∧ x1 ^ 2 + b * x1 + 2 = 0 ∧ 2 * x2 ^ 3 + a * x2 - 12 = 0 ∧ x2 ^ 2 + b * x2 + 2 = 0} = {(-14, 3)} := by
  ext ⟨a, b⟩
  simp [-one_div]
  constructor
  · -- First prove {(a, b) : ∃ x1 x2, x1 ≠ x2 ∧ 2x₁³+ax₁-12=0 ∧ ...} ⊆ {(-14, 3)}.
    rintro ⟨x1, x2, h12, h1, h2, h3, h4⟩
    have eq1 : 2 * (x1 ^ 2 + x1 * x2 + x2 ^ 2) + a = 0 := by
      have h5 : 2 * (x1 ^ 3 - x2 ^ 3) + a * (x1 - x2) = 0 := by linarith
      have h5' : (x1 - x2) ≠ 0 := sub_ne_zero_of_ne h12
      have h6 : 2 * (x1 ^ 2 + x1 * x2 + x2 ^ 2) + a = 0 := by
        apply (mul_left_inj' h5').mp
        linarith
      linarith
    have eq2 : x1 + x2 + b = 0 := by
      have h6 : (x1 ^ 2 - x2 ^ 2) + b * (x1 - x2) = 0 := by linarith
      have h5' : (x1 - x2) ≠ 0 := sub_ne_zero_of_ne h12
      have h7 : x1 + x2 + b = 0 := by
        apply (mul_left_inj' h5').mp
        linarith
      linarith
    -- Now we need to get the values of b and a by further manipulations.
    have eq5 : x1 + x2 = -3 := by
      nlinarith [sq_pos_of_ne_zero (show (x1 - x2 : ℝ) ≠ 0 by
        by_contra h
        have : x1 = x2 := by linarith
        contradiction), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2), sq_nonneg (x1 * x2)]
    -- Now, we solve for b.
    have eq6 : b = 3 := by
      linarith [eq2, eq5]
    -- Now we can prove x1 * x2 = 2
    have eq7 : x1 * x2 = 2 := by
      nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 + x2), sq_nonneg (x1 * x2), eq5, h1, h2, h3, h4]
    -- Now we solve for a.
    have eq8 : a = -14 := by
      nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 * x2), sq_nonneg (x1 + x2), eq1, eq5, eq7]
    simp [eq6, eq8]
  · -- Show that (-14, 3) are in the left side
    rintro (⟨rfl, rfl⟩)
    use -1, -2
    constructor
    · -- Show x1 ≠ x2
      norm_num
    constructor
    · -- Show 2 * x1 ^ 3 + a * x1 - 12 = 0
      norm_num
    constructor
    · -- Show x1 ^ 2 + b * x1 + 2 = 0
      norm_num
    constructor
    · -- Show 2 * x2 ^ 3 + a * x2 - 12 = 0
      norm_num
    · -- Show x2 ^ 2 + b * x2 + 2 = 0
      norm_num