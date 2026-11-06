import Mathlib

theorem algebra_98849 {x y : ℝ} (h : x^2 - 2 * Real.sqrt 3 * x + y^2 + 4 * y + 3 = 0)
    (h' : ⌊x⌋ = ⌊y⌋) :
    ⌊x⌋ = -1 ∨ ⌊x⌋ = 0 := by
  have h1 : (x - Real.sqrt 3)^2 + (y + 2)^2 = 4 := by
    nlinarith [h, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h2 : Real.sqrt 3 ^ 2 = 3 := by 
    exact Real.sq_sqrt (by norm_num) 
  have h3 : (x - Real.sqrt 3) ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg (y + 2)]
  have h8 : (y + 2) ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg (x - Real.sqrt 3)]
  have h4 : -2 ≤ x - Real.sqrt 3 := by nlinarith [sq_nonneg (x - Real.sqrt 3)]
  have h5 : x - Real.sqrt 3 ≤ 2 := by nlinarith [sq_nonneg (x - Real.sqrt 3)]
  have h6 : -2 ≤ y + 2 := by nlinarith [sq_nonneg (y + 2)]
  have h7 : y + 2 ≤ 2 := by nlinarith [sq_nonneg (y + 2)]
  have hx1 : Real.sqrt 3 - 2 ≤ x := by linarith
  have hx2 : x ≤ Real.sqrt 3 + 2 := by linarith
  have hy1 : -4 ≤ y := by nlinarith
  have hy2 : y ≤ 0 := by nlinarith
  have h9 : ⌊x⌋ ≤ 3 := by
    have h10 : x ≤ Real.sqrt 3 + 2 := by linarith
    have h11 : Real.sqrt 3 + 2 < (4 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    by_contra h
    push_neg at h
    have h13 : x ≥ (4 : ℝ) := by
      have h14 : ⌊x⌋ ≥ 4 := by omega
      have h15 : x ≥ (⌊x⌋ : ℝ) := by exact Int.floor_le x
      have h16 : (⌊x⌋ : ℝ) ≥ (4 : ℝ) := by exact_mod_cast h14
      nlinarith
    nlinarith
  have h10 : ⌊x⌋ ≥ -1 := by
    have h11 : x ≥ Real.sqrt 3 - 2 := by linarith
    have h12 : Real.sqrt 3 - 2 > (-2 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    by_contra h
    push_neg at h
    have h13 : x < (-2 : ℝ) := by
      have h14 : ⌊x⌋ ≤ -2 := by omega
      have h15 : x < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x
      have h16 : (⌊x⌋ + 1 : ℝ) ≤ ( -1 : ℝ) := by
        have h17 : ⌊x⌋ ≤ -2 := by omega
        have h18 : (⌊x⌋ : ℝ) ≤ (-2 : ℝ) := by exact_mod_cast h17
        nlinarith
      nlinarith
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h11 : ⌊y⌋ ≤ 0 := by
    have h12 : y ≤ (0 : ℝ) := by linarith
    have h13 : ⌊y⌋ ≤ 0 := by
      by_contra h
      push_neg at h
      have h14 : y ≥ (1 : ℝ) := by
        have h15 : ⌊y⌋ ≥ 1 := by omega
        have h16 : y ≥ (⌊y⌋ : ℝ) := by exact Int.floor_le y
        have h17 : (⌊y⌋ : ℝ) ≥ (1 : ℝ) := by exact_mod_cast h15
        nlinarith
      nlinarith
    omega
  have h14 : ⌊y⌋ ≥ -4 := by
    have h15 : y ≥ (-4 : ℝ) := by linarith
    have h16 : ⌊y⌋ ≥ -4 := by
      by_contra h
      push_neg at h
      have h17 : y < (-4 : ℝ) := by
        have h18 : ⌊y⌋ ≤ -5 := by omega
        have h19 : y < (⌊y⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one y
        have h20 : (⌊y⌋ + 1 : ℝ) ≤ (-4 : ℝ) := by
          have h21 : ⌊y⌋ ≤ -5 := by omega
          have h22 : (⌊y⌋ : ℝ) ≤ (-5 : ℝ) := by exact_mod_cast h21
          nlinarith
        nlinarith
      linarith
    omega
  omega