import Mathlib



theorem inequalities_290816 :
  IsLeast {s : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x^2 + y^2 + z^2 = 1 ∧ s = (x * y) / z + (y * z) / x + (z * x) / y} (Real.sqrt 3) := by
  constructor
  · -- Show that Real.sqrt 3 is in the set
    use Real.sqrt 3 / 3, Real.sqrt 3 / 3, Real.sqrt 3 / 3
    constructor
    · -- Show x > 0
      positivity
    constructor
    · -- Show y > 0
      positivity
    constructor
    · -- Show z > 0
      positivity
    constructor
    · -- Show x^2 + y^2 + z^2 = 1
      have h1 : (Real.sqrt 3 / 3 : ℝ) ^ 2 = (3 : ℝ) / 9 := by
        calc
          (Real.sqrt 3 / 3 : ℝ) ^ 2 = (Real.sqrt 3) ^ 2 / 9 := by ring_nf
          _ = (3 : ℝ) / 9 := by
            rw [Real.sq_sqrt]
            all_goals norm_num
      nlinarith
    · -- Show s = (x * y) / z + (y * z) / x + (z * x) / y
      have h1 : (Real.sqrt 3 / 3 : ℝ) * (Real.sqrt 3 / 3) / (Real.sqrt 3 / 3) = Real.sqrt 3 / 3 := by
        field_simp
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      nlinarith [h1]
  · -- Show that Real.sqrt 3 is the least
    intro s hs
    rcases hs with ⟨x, y, z, hx, hy, hz, h1, heq⟩
    have h2 : ((x * y) / z + (y * z) / x + (z * x) / y) ^ 2 ≥ 3 := by
      have h3 : ((x * y) / z + (y * z) / x + (z * x) / y) ^ 2 =
        ((x * y) / z)^2 + ((y * z) / x)^2 + ((z * x) / y)^2 + 2 * (( (x * y) / z ) * ( (y * z) / x ) + ( (x * y) / z ) * ( (z * x) / y ) + ( (y * z) / x ) * ( (z * x) / y )) := by ring
      have h4 : ( (x * y) / z ) * ( (y * z) / x ) = y^2 := by
        field_simp
        <;> ring
      have h5 : ( (x * y) / z ) * ( (z * x) / y ) = x^2 := by
        field_simp
        <;> ring
      have h6 : ( (y * z) / x ) * ( (z * x) / y ) = z^2 := by
        field_simp
        <;> ring
      have h7 : ((x * y) / z + (y * z) / x + (z * x) / y) ^ 2 =
        ((x * y) / z)^2 + ((y * z) / x)^2 + ((z * x) / y)^2 + 2 * (y ^ 2 + x ^ 2 + z ^ 2) := by
        rw [h3]
        rw [h4, h5, h6]
        all_goals ring
      have h8 : ((x * y) / z + (y * z) / x + (z * x) / y) ^ 2 ≥ 3 := by
        have h2' : x ^ 2 + y ^ 2 + z ^ 2 = 1 := h1
        nlinarith [sq_nonneg ((x * y) / z - (y * z) / x), sq_nonneg ((x * y) / z - (z * x) / y), sq_nonneg ((y * z) / x - (z * x) / y), sq_nonneg (x^2 - y^2), sq_nonneg (x^2 - z^2), sq_nonneg (y^2 - z^2)]
      linarith
    have h3 : ((x * y) / z + (y * z) / x + (z * x) / y) ≥ Real.sqrt 3 := by
      have h4 : ((x * y) / z + (y * z) / x + (z * x) / y) ^ 2 ≥ 3 := h2
      have h5 : Real.sqrt 3 ≥ 0 := by positivity
      have h6 : ((x * y) / z + (y * z) / x + (z * x) / y) ≥ 0 := by positivity
      have h7 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      nlinarith [Real.sqrt_nonneg 3, sq_nonneg (( (x * y) / z + (y * z) / x + (z * x) / y) - Real.sqrt 3)]
    linarith [heq, h3]