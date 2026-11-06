import Mathlib

theorem algebra_69825 {x y : ℝ} (h : {(x, y) : ℝ × ℝ | (y^2 + 6) * (x - 1) = y * (x^2 + 1) ∧ (x^2 + 6) * (y - 1) = x * (y^2 + 1)}.Finite) : Even {(x, y) : ℝ × ℝ | (y^2 + 6) * (x - 1) = y * (x^2 + 1) ∧ (x^2 + 6) * (y - 1) = x * (y^2 + 1)}.ncard := by

  have h1 : {(x, y) : ℝ × ℝ | (y^2 + 6) * (x - 1) = y * (x^2 + 1) ∧ (x^2 + 6) * (y - 1) = x * (y^2 + 1)} = {(2, 2), (2, 3), (3, 2), (3, 3)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume h
      rintro ⟨h1, h2⟩
      have h3 : (x - 2) * (x - 3) = 0 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (x - 3), sq_nonneg (y - 2), sq_nonneg (y - 3), sq_nonneg (x * y), sq_nonneg (x - y)]
      cases' (mul_eq_zero.mp h3) with h4 h5
      · -- Case h4 : x - 2 = 0 so x = 2.
        have hx : x = 2 := by linarith
        have hy_sqr : (y - 2) * (y - 3) = 0 := by
          rw [hx] at h1 h2
          nlinarith
        cases' (mul_eq_zero.mp hy_sqr) with h7 h8
        · -- Assume h7
          have hy : y = 2 := by linarith
          simp [hx, hy]
        · -- Assume h8
          have hy : y = 3 := by linarith
          simp [hx, hy]
      · -- Case h5 : x - 3 = 0 so x = 3.
        have hx : x = 3 := by linarith
        have hy_sqr : (y - 2) * (y - 3) = 0 := by
          rw [hx] at h1 h2
          nlinarith
        cases' (mul_eq_zero.mp hy_sqr) with h7 h8
        · -- Assume h7
          have hy : y = 2 := by linarith
          simp [hx, hy]
        · -- Assume h8
          have hy : y = 3 := by linarith
          simp [hx, hy]

    · -- Show rintro (2,2) etc., implies solutions.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (2, 2)
        constructor
        · -- First equation
          norm_num
        · -- Second equation
          norm_num
      · -- (2, 3)
        constructor
        · -- First equation
          norm_num
        · -- Second equation
          norm_num
      · -- (3, 2)
        constructor
        · -- First equation
          norm_num
        · -- Second equation
          norm_num
      · -- (3, 3)
        constructor
        · -- First equation
          norm_num
        · -- Second equation
          norm_num

  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> native_decide