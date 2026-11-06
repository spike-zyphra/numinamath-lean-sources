import Mathlib

theorem algebra_252631 :
  { (x, y, z) : ℝ × ℝ × ℝ | x^4 * (y^2 - z^2) = 243 ∧ y^4 * (z^2 - x^2) = -128 ∧ z^4 * (x^2 - y^2) = 5 } =
  { (3, 2, 1), (3, 2, -1), (3, -2, 1), (3, -2, -1), (-3, 2, 1), (-3, 2, -1), (-3, -2, 1), (-3, -2, -1) } := by 
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- (x, y, z) in the left implies (x, y, z) in the right 
    rintro ⟨h1, h2, h3⟩
    have eq1 : x^4 = 81 := by
      nlinarith [sq_nonneg (x^2 - 9), sq_nonneg (y^2 - 4), sq_nonneg (z^2 - 1), 
            sq_nonneg (x^2 * y^2), sq_nonneg (x^2 * z^2), sq_nonneg (y^2 * z^2),
            h1, h2, h3, 
            sq_nonneg (x * y), sq_nonneg (x * z), sq_nonneg (y * z)]
    have eq2 : y^4 = 16 := by
      nlinarith [sq_nonneg (x^2 - 9), sq_nonneg (y^2 - 4), sq_nonneg (z^2 - 1), 
            sq_nonneg (x^2 * y^2), sq_nonneg (x^2 * z^2), sq_nonneg (y^2 * z^2),
            h1, h2, h3, 
            sq_nonneg (x * y), sq_nonneg (x * z), sq_nonneg (y * z)]
    have eq3 : z^4 = 1 := by
      nlinarith [sq_nonneg (x^2 - 9), sq_nonneg (y^2 - 4), sq_nonneg (z^2 - 1), 
            sq_nonneg (x^2 * y^2), sq_nonneg (x^2 * z^2), sq_nonneg (y^2 * z^2),
            h1, h2, h3, 
            sq_nonneg (x * y), sq_nonneg (x * z), sq_nonneg (y * z)]
    have hx2 : x^2 = 9 := by
      have hx4_nonneg : x^4 ≥ 0 := by positivity
      have hx4_eq : x^4 = 81 := eq1
      nlinarith [sq_nonneg (x^2 - 9), sq_nonneg (x^2 * x^2 - 81)]
    have hy2 : y^2 = 4 := by
      have hy4_nonneg : y^4 ≥ 0 := by positivity
      have hy4_eq : y^4 = 16 := eq2
      nlinarith [sq_nonneg (y^2 - 4), sq_nonneg (y^2 * y^2 - 16)]
    have hz2 : z^2 = 1 := by
      have hz4_nonneg : z^4 ≥ 0 := by positivity
      have hz4_eq : z^4 = 1 := eq3
      nlinarith [sq_nonneg (z^2 - 1), sq_nonneg (z^2 * z^2 - 1)]
    have hx_eq : x = 3 ∨ x = -3 := by
      have h11 : x^2 = 9 := hx2
      have h22 : x^2 - 9 = 0 := by linarith
      have h33 : (x - 3) * (x + 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h33) with h44 h55
      · -- Case x - 3 = 0
        left
        linarith
      · -- Case x + 3 = 0
        right
        nlinarith
    have hy_eq : y = 2 ∨ y = -2 := by
      have h11 : y^2 = 4 := hy2
      have h22 : y^2 - 4 = 0 := by linarith
      have h33 : (y - 2) * (y + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h33) with h44 h55
      · -- Case y - 2 = 0
        left
        linarith
      · -- Case y + 2 = 0
        right
        nlinarith
    have hz_eq : z = 1 ∨ z = -1 := by
      have h11 : z^2 = 1 := hz2
      have h22 : z^2 - 1 = 0 := by linarith
      have h33 : (z - 1) * (z + 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h33) with h44 h55
      · -- Case z - 1 = 0
        left
        linarith
      · -- Case z + 1 = 0
        right
        nlinarith
    rcases hx_eq with hx | hx <;> rcases hy_eq with hy | hy <;> rcases hz_eq with hz | hz <;> 
      simp [hx, hy, hz] at *
      <;> norm_num [hx, hy, hz] at *
      <;> tauto
  · -- (x, y, z) in the right implies (x, y, z) in the left 
    rintro (h | h | h | h | h | h | h | h)
    · -- (3, 2, 1)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num
    · -- (3, 2, -1)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num
    · -- (3, -2, 1)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num
    · -- (3, -2, -1)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num
    · -- (-3, 2, 1)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num
    · -- (-3, 2, -1)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num
    · -- (-3, -2, 1)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num
    · -- (-3, -2, -1)
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num