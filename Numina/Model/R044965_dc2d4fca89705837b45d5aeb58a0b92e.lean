import Mathlib

theorem algebra_313529 (x : ℝ) (hx : x = 1 / (Real.sqrt 2 - 1)) (a b : ℝ)
    (ha : a = x - ⌊x⌋) (hb : b = -x - ⌊-x⌋) :
    a^3 + b^3 + 3 * a * b = 1 := by

  have hx2 : x = Real.sqrt 2 + 1 := by
    rw [hx]
    have h1 : Real.sqrt 2 - 1 ≠ 0 := by 
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    field_simp [h1]
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]

  have hx3 : ⌊x⌋ = 2 := by 
    rw [hx2]
    have h1 : 2 < Real.sqrt 2 + 1 := by 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
    have h2 : Real.sqrt 2 + 1 < (3 : ℝ) := by 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> try nlinarith

  have ha2 : a = Real.sqrt 2 - 1 := by 
    rw [ha, hx3, hx2]
    all_goals ring_nf 

  -- Compute floor of -x
  have hx4 : ⌊-x⌋ = -3 := by 
    rw [hx2]
    have h3 : - (Real.sqrt 2 + 1) < (-2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    have h4 : - (Real.sqrt 2 + 1) > (-3 : ℝ) := by 
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> try nlinarith

  have hb2 : b = (2 : ℝ) - Real.sqrt 2 := by 
    rw [hb, hx4, hx2]
    all_goals ring_nf 

  have hab : a + b = 1 := by 
    rw [ha2, hb2]
    all_goals ring_nf 

  have eq1 : a ^ 3 + b ^ 3 + 3 * a * b = 1 := by 
    have h1 : a + b = 1 := hab 
    have h2 : a ^ 3 + b ^ 3 = (a + b) ^ 3 - 3 * a * b * (a + b) := by 
      ring
    rw [h2, h1]
    all_goals
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]

  linarith [eq1]