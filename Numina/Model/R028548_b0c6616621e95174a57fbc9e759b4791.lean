import Mathlib

theorem algebra_218893 :
    {(x, y, z) : ℝ × ℝ × ℝ | 0 < x ∧ 0 < y ∧ 0 < z ∧
    x^2 + y^2 + x * y = 7 ∧
    x^2 + z^2 + x * z = 13 ∧
    y^2 + z^2 + y * z = 19} = 
    {(1, 2, 3)} := by 
  ext ⟨x, y, z⟩ 
  simp
  constructor 
  · -- Forward direction: the system constraints imply (1, 2, 3)
    rintro ⟨hx, hy, hz, h1, h2, h3⟩
    have h4 : (z - y) * (x + y + z) = 6 := by 
      nlinarith 
    have h5 : (z - x) * (x + y + z) = 12 := by 
      nlinarith 
    have h6 : z - x = 2 * (z - y) := by 
      nlinarith 
    have h7 : z = 2 * y - x := by 
      nlinarith 
    have eq1 : y ^ 2 + (2 * y - x) ^ 2 + y * (2 * y - x) = 19 := by 
      rw [show z = 2 * y - x by linarith [h7]] at h3 
      linarith 
    have eq2 : (x - 1) ^ 2 + (y - 2) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 2), sq_nonneg (x ^ 2 + y ^ 2 -7), sq_nonneg (y ^ 2 + (2 * y - x) ^ 2 - 19), sq_pos_of_pos hx, sq_pos_of_pos hy, mul_pos hx hy]
    have hx1 : x = 1 := by 
      nlinarith 
    have hy2 : y = 2 := by 
      nlinarith 
    have hz3 : z = 3 := by 
      rw [hx1, hy2] at h7 
      linarith 
    simp [hx1, hy2, hz3] 
  · -- Backward direction: (1, 2, 3) satisfies the system.
    rintro ⟨rfl, rfl, rfl⟩
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