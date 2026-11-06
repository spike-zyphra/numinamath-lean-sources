import Mathlib

theorem algebra_11065 :
  {x | x - 1 ≥ 0 ∧ x + 3 - 4 * √(x - 1) ≥ 0 ∧ x + 8 - 6 * √(x - 1) ≥ 0 ∧
      √(x + 3 - 4 * √(x - 1)) + √(x + 8 - 6 * √(x - 1)) = 1} =
  Set.Icc 5 10 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · intro hx 
    rcases hx with ⟨hx1,hx2,hx3,hx4⟩
    let y : ℝ := √ (x - 1)
    have hy1 : y ^ 2 = x - 1 := Real.sq_sqrt (by linarith [hx1])
    have hy2 : x = y ^ 2 + 1 := by linarith
    rw [hy2] at hx4
    have hy3 : √ (y ^ 2) = y := congrArg Real.sqrt hy1
    simp [hy3] at hx4
    ring_nf at hx4
    have hy4 : √((y-2)^2) + √((y-3)^2) = 1 := by rw [← hx4] ;ring_nf
    by_cases h1 : y < 2
    · -- If y < 2, then √((y - 2)^2) = 2 - y and √((y - 3)^2) = 3 - y
      have h2 : √((y - 2) ^ 2) = 2 - y := by
        refine Real.sqrt_eq_cases.mpr ?_
        left 
        ring_nf 
        simp 
        all_goals nlinarith [sq_nonneg (y - 2), sq_nonneg (y)]
      have h3 : √((y - 3) ^ 2) = 3 - y := by 
        refine Real.sqrt_eq_cases.mpr ?_
        left 
        ring_nf 
        simp 
        all_goals nlinarith [sq_nonneg (y - 3), sq_nonneg (y)]
      rw [h2, h3] at hy4
      all_goals nlinarith
    · -- If y ≥ 2
      by_cases h4 : y > 3
      · -- If y > 3, then √((y - 2)^2) = y - 2 and √((y - 3)^2) = y - 3
        have h5 : √((y - 2) ^ 2) = y - 2 := by
          refine Real.sqrt_sq ?_
          nlinarith 
        have h6 : √((y - 3) ^ 2) = y - 3 := by 
          refine Real.sqrt_sq ?_
          nlinarith 
        rw [h5, h6] at hy4 
        all_goals nlinarith
      · -- If 2 ≤ y ≤ 3 
        constructor 
        · -- Show that 5 ≤ x 
          have h5 : 2 ≤ y := by linarith 
          have h6 : y ≤ 3 := by linarith 
          nlinarith 
        · -- Show that x ≤ 10 
          have h5 : 2 ≤ y := by linarith 
          have h6 : y ≤ 3 := by linarith 
          nlinarith 
  · -- Prove the reverse direction: if x ∈ [5, 10], then all conditions hold.
    rintro ⟨hx1, hx2⟩
    have hx1: x - 1 ≥ 0 := by linarith
    have hx5 : 4 ≤ x - 1 := by linarith 
    have hx6 : x - 1 ≤ 9 := by linarith 
    have hx7 : 2 ≤ Real.sqrt (x - 1) := by 
      have h10 : Real.sqrt (x - 1) ≥ Real.sqrt 4 := by
        apply Real.sqrt_le_sqrt
        linarith
      have h11 : Real.sqrt 4 = 2 := Real.sqrt_eq_cases.mpr (by norm_num)
      linarith 
    have hx8 : Real.sqrt (x - 1) ≤ 3 := by
      have h13 : Real.sqrt (x - 1) ≤ Real.sqrt 9 := by 
        apply Real.sqrt_le_sqrt 
        linarith 
      have h14 : Real.sqrt 9 = 3 := Real.sqrt_eq_cases.mpr (by norm_num)
      linarith
    constructor 
    · -- Show that x - 1 ≥ 0
      linarith 
    constructor 
    · -- Show that x + 3 - 4 * √(x - 1) ≥ 0 
      nlinarith [sq_nonneg (Real.sqrt (x - 1) - 2), sq_nonneg (Real.sqrt (x - 1) - 3), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    constructor
    · -- Show that x + 8 - 6 * √(x - 1) ≥ 0 
      nlinarith [sq_nonneg (Real.sqrt (x - 1) - 3), sq_nonneg (Real.sqrt (x - 1) - 2), Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
    · -- Show that √(x + 3 - 4 * √(x - 1)) + √(x + 8 - 6 * √(x - 1)) = 1 
      have h1 : Real.sqrt (x + 3 - 4 * Real.sqrt (x - 1)) + Real.sqrt (x + 8 - 6 * Real.sqrt (x - 1)) = 1 := by
        have h2 : Real.sqrt (x + 3 - 4 * Real.sqrt (x - 1)) = Real.sqrt (x - 1) - 2 := by
          have h5 : (Real.sqrt (x - 1) - 2 : ℝ) ^ 2 = x + 3 - 4 * Real.sqrt (x - 1) := by 
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
          have h6 : 0 ≤ Real.sqrt (x - 1) - 2 := by linarith 
          have h7 : Real.sqrt (x + 3 - 4 * Real.sqrt (x - 1)) = Real.sqrt (x - 1) - 2 := by 
            rw [show x + 3 - 4 * Real.sqrt (x - 1) = (Real.sqrt (x - 1) - 2) ^ 2 by linarith [h5]]
            rw [Real.sqrt_sq (show 0 ≤ Real.sqrt (x - 1) - 2 by linarith)]
          linarith
        have h3 : Real.sqrt (x + 8 - 6 * Real.sqrt (x - 1)) = 3 - Real.sqrt (x - 1) := by
          have h8 : (3 - Real.sqrt (x - 1) : ℝ) ^ 2 = x + 8 - 6 * Real.sqrt (x - 1) := by 
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)]
          have h9 : 0 ≤ 3 - Real.sqrt (x - 1) := by linarith 
          have h10 : Real.sqrt (x + 8 - 6 * Real.sqrt (x - 1)) = 3 - Real.sqrt (x - 1) := by
            have h10a : (3 - Real.sqrt (x - 1) : ℝ) ^ 2 = x + 8 - 6 * Real.sqrt (x - 1) := h8 
            have h11 : 0 ≤ 3 - Real.sqrt (x - 1) := h9 
            rw [show x + 8 - 6 * Real.sqrt (x - 1) = (3 - Real.sqrt (x - 1)) ^ 2 by linarith [h10a]]
            rw [Real.sqrt_sq (show 0 ≤ 3 - Real.sqrt (x - 1) by linarith)]
          linarith
        rw [h2, h3]
        all_goals nlinarith
      linarith