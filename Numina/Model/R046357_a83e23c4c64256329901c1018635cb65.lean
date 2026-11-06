import Mathlib

theorem algebra_225957 :
    {(x, y, z) : ℝ × ℝ × ℝ | x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ 
    x + 15 ≠ 0 ∧ y - 6 ≠ 0 ∧ x + 24 ≠ 0 ∧ y - 15 ≠ 0 ∧ 
    x + y + 9 ≠ 0 ∧ 1/x + 1/y = 1/z ∧ 
    1/(x + 15) + 1/(y - 6) = 1/z ∧ 
    1/(x + 24) + 1/(y - 15) = 1/z} = 
    {(-20, 10, 20), (-60, -30, -20)} := by
  ext ⟨x, y, z⟩
  simp [-one_div]
  constructor
  · -- Assume (x, y, z) in the left side, prove in the right
    rintro ⟨hx, hy, hz, hx15, hy6, hx24, hy15, hxy9, h1, h2, h3⟩
    have eq1 : y * z + x * z = x * y := by
      field_simp [hx, hy, hz] at h1
      nlinarith
    have eq2 : (y - 6) * z + (x + 15) * z = (x + 15) * (y - 6) := by
      field_simp [show x + 15 ≠ 0 by assumption, show y - 6 ≠ 0 by assumption, hz] at h2
      nlinarith
    have eq3 : (y - 15) * z + (x + 24) * z = (x + 24) * (y - 15) := by
      field_simp [show x + 24 ≠ 0 by assumption, show y - 15 ≠ 0 by assumption, hz] at h3
      nlinarith
    have eq4 : x = y - 30 := by
      nlinarith [eq2, eq3]
    -- Substitute x = y - 30 into eq1
    have eq5 : (2 * y - 30) * z = y^2 - 30 * y := by
      rw [show x = y - 30 by linarith [eq4] ] at eq1
      nlinarith
    -- eq6 is from eq2 substituting x = y - 30
    have eq6 : (2 * y - 21) * z = y^2 - 21 * y + 90 := by
      rw [show x = y - 30 by linarith [eq4] ] at eq2
      nlinarith
    -- eq7 z = y + 10
    have eq7 : z = y + 10 := by
      nlinarith [eq5, eq6]
    -- eq8 quadratic
    have eq8 : y^2 + 20 * y - 300 = 0 := by
      rw [show z = y + 10 by linarith [eq7] ] at eq5
      nlinarith
    have eq9 : (y - 10) * (y + 30) = 0 := by
      nlinarith [eq8]
    cases' (mul_eq_zero.1 eq9) with hy10 hy30
    · -- y = 10
      have eq11 : y = 10 := by linarith
      have eq12 : x = -20 := by linarith [eq4, eq11]
      have eq13 : z = 20 := by linarith [eq7, eq11]
      left
      simp [eq12, eq11, eq13]
    · -- y + 30 = 0, so y = -30
      have eq14 : y = -30 := by linarith
      have eq15 : x = -60 := by linarith [eq4, eq14]
      have eq16 : z = -20 := by linarith [eq7, eq14]
      right
      simp [eq15, eq14, eq16]
  · -- Show that the solutions in the right side satisfy the system.
    rintro (h | h)
    · -- (-20, 10, 20)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- (-60, -30, -20)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num