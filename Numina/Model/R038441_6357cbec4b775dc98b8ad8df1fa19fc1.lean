import Mathlib

open BigOperators Real Set

theorem algebra_224028 :
  IsLeast {a | ∃ x y : ℝ, x ∈ Icc 1 3 ∧ y ∈ Icc 1 3 ∧
    a = ((3 * x * y + x ^ 2) * sqrt (3 * x * y + x - 3 * y) +
          (3 * x * y + y ^ 2) * sqrt (3 * x * y + y - 3 * x)) /
    (x ^ 2 * y + y ^ 2 * x)} 4 := by
  constructor
  · -- Show 4 is in the set
    use 1, 1
    constructor
    · -- Show 1 ∈ Icc 1 3
      norm_num [mem_Icc]
    constructor
    · -- Show 1 ∈ Icc 1 3
      norm_num [mem_Icc]
    · -- Show 4 = (...)
      have h1 : sqrt (1 : ℝ) = 1 := by
        rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      norm_num [h1]
  · -- Show that 4 is the least element
    intro a ha
    rcases ha with ⟨x, y, hx, hy, ha⟩
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with ⟨hy1, hy2⟩
    have h1 : 0 ≤ 3 * x * y + x - 3 * y := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1), mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - y by linarith)), mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - x by linarith)), mul_nonneg (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - x by linarith)) (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - y by linarith))]
    have h2 : 0 ≤ 3 * x * y + y - 3 * x := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1), mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - y by linarith)), mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - x by linarith)), mul_nonneg (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - x by linarith)) (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - y by linarith))]
    have h3 : (3 * x * y + x ^ 2) * sqrt (3 * x * y + x - 3 * y) + (3 * x * y + y ^ 2) * sqrt (3 * x * y + y - 3 * x) ≥ 4 * (x ^ 2 * y + y ^ 2 * x) := by
      have h4 : sqrt (3 * x * y + x - 3 * y) ≥ (x : ℝ) := by
        have h6 : (x : ℝ) ^ 2 ≤ (3 * x * y + x - 3 * y : ℝ) := by
          nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1), mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - y by linarith)), mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - x by linarith)), mul_nonneg (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - x by linarith)) (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - y by linarith))]
        have h7 : (x : ℝ) ≤ sqrt (3 * x * y + x - 3 * y : ℝ) := by
          apply Real.le_sqrt_of_sq_le
          linarith
        linarith
      have h8 : sqrt (3 * x * y + y - 3 * x) ≥ (y : ℝ) := by
        have h9 : (y : ℝ) ^ 2 ≤ (3 * x * y + y - 3 * x : ℝ) := by
          nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1), mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - y by linarith)), mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - x by linarith)), mul_nonneg (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - x by linarith)) (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - y by linarith))]
        have h10 : (y : ℝ) ≤ sqrt (3 * x * y + y - 3 * x : ℝ) := by
          apply Real.le_sqrt_of_sq_le
          linarith
        linarith
      have h12 : (3 * x * y + x ^ 2) * sqrt (3 * x * y + x - 3 * y) ≥ (3 * x * y + x ^ 2) * (x : ℝ) := by
        have h13 : sqrt (3 * x * y + x - 3 * y) ≥ (x : ℝ) := by
          linarith [h4]
        have h14 : 0 ≤ (3 * x * y + x ^ 2 : ℝ) := by nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]
        nlinarith
      have h15 : (3 * x * y + y ^ 2) * sqrt (3 * x * y + y - 3 * x) ≥ (3 * x * y + y ^ 2) * (y : ℝ) := by
        have h16 : sqrt (3 * x * y + y - 3 * x) ≥ (y : ℝ) := by
          linarith [h8]
        have h17 : 0 ≤ (3 * x * y + y ^ 2 : ℝ) := by nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1)]
        nlinarith
      have h18 : (3 * x * y + x ^ 2) * (x : ℝ) + (3 * x * y + y ^ 2) * (y : ℝ) ≥ 4 * (x ^ 2 * y + y ^ 2 * x) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1), mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - y by linarith)), mul_nonneg (sub_nonneg.mpr hy1) (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - x by linarith)), mul_nonneg (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - x by linarith)) (sub_nonneg.mpr (show (0 : ℝ) ≤ 3 - y by linarith)), sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1)]
      linarith [h12, h15, h18]
    have h4 : 0 < (x ^ 2 * y + y ^ 2 * x : ℝ) := by
      have h11 : 0 < x := by linarith
      have h12 : 0 < y := by linarith
      positivity
    have h5 : ((3 * x * y + x ^ 2) * sqrt (3 * x * y + x - 3 * y) + (3 * x * y + y ^ 2) * sqrt (3 * x * y + y - 3 * x)) / (x ^ 2 * y + y ^ 2 * x) ≥ (4 : ℝ) := by
      have h41 : (3 * x * y + x ^ 2) * sqrt (3 * x * y + x - 3 * y) + (3 * x * y + y ^ 2) * sqrt (3 * x * y + y - 3 * x) ≥ 4 * (x ^ 2 * y + y ^ 2 * x) := by
        linarith [h3]
      have h14 : 0 < (x ^ 2 * y + y ^ 2 * x : ℝ) := by
        have h11 : 0 < x := by linarith
        have h12 : 0 < y := by linarith
        positivity
      apply (le_div_iff₀ (by positivity)).mpr
      linarith
    linarith [ha, h5]