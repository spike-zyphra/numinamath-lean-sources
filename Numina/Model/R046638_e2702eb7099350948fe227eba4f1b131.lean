import Mathlib

theorem algebra_211673 : {(a, b, c) : ℤ × ℤ × ℤ | a + b + c = 24 ∧ a ^ 2 + b ^ 2 + c ^ 2 = 210 ∧ a * b * c = 440} = {(5, 8, 11), (5, 11, 8), (8, 5, 11), (8, 11, 5), (11, 5, 8), (11, 8, 5)}:= by 
  ext ⟨a, b, c⟩ 
  simp [-one_div]
  constructor
  · -- Assume h
    rintro ⟨h1, h2, h3⟩
    have h4 : a ≤ 24 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    have h5 : b ≤ 24 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    have h6 : c ≤ 24 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    have h7 : a ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c)]
    have h8 : b ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c)]
    have h9 : c ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c)]
    interval_cases a <;> interval_cases b <;> omega
  · -- Assume direction
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · -- Check that (5, 8, 11) is a solution
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Check that (5, 11, 8) is a solution
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Check that (8, 5, 11) is a solution
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Check that (8, 11, 5) is a solution
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Check that (11, 5, 8) is a solution
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Check that (11, 8, 5) is a solution
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num