import Mathlib

theorem algebra_176997 {x y : ℝ} (hx : x = ⌊5 - Real.sqrt 3⌋) (hy : y = (5 - Real.sqrt 3) - x) :
    2 * x^3 - (y^3 + 1 / y^3) = 2 := by 
  have h1 : ⌊5 - Real.sqrt 3⌋ = 3 := by
    have h1 : 1 < Real.sqrt 3 := by
      rw [Real.lt_sqrt] <;> norm_num
    have h5 : Real.sqrt 3 < 2 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), show (2 : ℝ)^2 > (3 : ℝ) by norm_num]
    have h6 : 3 < 5 - Real.sqrt 3 := by
      nlinarith [h5, Real.sqrt_nonneg 3]
    have h7 : 5 - Real.sqrt 3 < 4 := by
      nlinarith [h1, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  have hx2 : x = 3 := by
    rw [hx]
    exact_mod_cast h1
  have hy2 : y = (2 - Real.sqrt 3) := by
    rw [hy, hx2]
    nlinarith
  have hy3 : y^3 = 26 - 15 * Real.sqrt 3 := by
    rw [hy2]
    have h3 : (2 - Real.sqrt 3) ^ 3 = 26 - 15 * Real.sqrt 3 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (Real.sqrt 3 - 1)]
    exact h3
  have hy4 : (1 / y ^ 3 : ℝ) = (26 + 15 * Real.sqrt 3) := by
    have h9 : ((26 - 15 * Real.sqrt 3) : ℝ) ≠ 0 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h31 : y^3 = (26 - 15 * Real.sqrt 3 : ℝ) := hy3
    rw [h31]
    field_simp [h9]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (2 - Real.sqrt 3), sq_nonneg (2 + Real.sqrt 3)
    ]
  rw [hx2] 
  rw [show y^3 = (26 - 15 * Real.sqrt 3) by linarith [hy3]]
  have eq1 : (1 / (26 - 15 * Real.sqrt 3) : ℝ) = (26 + 15 * Real.sqrt 3) := by 
    have h11 : y^3 = (26 - 15 * Real.sqrt 3) := hy3
    have eq4 : (1 / y^3 : ℝ) = (26 + 15 * Real.sqrt 3) := hy4 
    have eq3 : (1 / (26 - 15 * Real.sqrt 3) : ℝ) = (1 / y^3 : ℝ) := by 
      rw [show (26 - 15 * Real.sqrt 3 : ℝ) = y^3 by linarith [h11]]
    linarith [eq4, eq3]
  rw [eq1]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  ]