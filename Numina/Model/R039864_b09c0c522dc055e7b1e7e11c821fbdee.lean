import Mathlib

theorem algebra_209539 :
  { (x, y) : ℝ × ℝ |
    x + y = x^2 + 2 * x * y + y^2 ∧
    x - y = x^2 - 2 * x * y + y^2 }
  =
  {(0, 0), (1, 0), (0.5, -0.5), (0.5, 0.5)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x, y) satisfy both equations.
    rintro ⟨h1, h2⟩
    have eq1 : (x + y) = (x + y) ^ 2 := by
      nlinarith
    have eq2 : (x - y) = (x - y) ^ 2 := by
      nlinarith
    have h3 : (x + y) * ((x + y) - 1) = 0 := by
      nlinarith
    have h4 : (x - y) * ((x - y) - 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h3) with h5 h6
    · 
      cases' (mul_eq_zero.mp h4) with h7 h8
      · -- Case (x + y) = 0 and (x - y) = 0:
        have h9 : x = 0 := by
          nlinarith [h5, h7]
        have h10 : y = 0 := by
          nlinarith [h5, h9]
        simp [h9, h10]
      · -- Case (x + y) = 0 and (x - y) - 1 = 0:
        have h9 : x = (0.5 : ℝ) := by
          nlinarith [h5, h8]
        have h10 : y = (-0.5 : ℝ) := by
          nlinarith [h5, h9, h8]
        simp [h9, h10]
    · 
      cases' (mul_eq_zero.mp h4) with h7 h8
      · -- Case (x + y) - 1 = 0 and (x - y) = 0:
        have h9 : x = (0.5 : ℝ) := by
          nlinarith [h6, h7]
        have h10 : y = (0.5 : ℝ) := by
          nlinarith [h7, h9, h6]
        simp [h9, h10]
      · -- Case (x + y) - 1 = 0 and (x - y) - 1 = 0:
        have h9 : x = (1 : ℝ) := by
          nlinarith [h6, h8]
        have h10 : y = (0 : ℝ) := by
          nlinarith [h8, h9, h6]
        simp [h9, h10]
  · -- Show that the four pairs satisfy the equations.
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · 
      constructor
      · norm_num
      · norm_num
    · 
      constructor
      · norm_num
      · norm_num
    · 
      constructor
      · norm_num
      · norm_num
    · 
      constructor
      · norm_num
      · norm_num