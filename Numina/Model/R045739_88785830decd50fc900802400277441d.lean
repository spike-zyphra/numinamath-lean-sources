import Mathlib

open Real Set

theorem algebra_207794 :
  IsGreatest {z : ℝ | ∃ x y : ℝ, x * y = z ∧
    (x ∈ Icc 0 12 ∧ y ∈ Icc 0 12) ∧
    (x * y = (12 - x) ^ 2 * (12 - y) ^ 2)} 81 := by
  constructor
  · -- Show 81 is in our set 
    use 9, 9
    constructor
    · -- Show 9 * 9 = 81
      norm_num
    constructor
    · -- Show x and y in closed interval [0,12]
      constructor
      · -- Show 9 in [0,12]
        norm_num [mem_Icc]
      · -- Show 9 in [0,12]
        norm_num [mem_Icc]
    · -- Show 9 * 9 = (12 - 9) ^ 2 * (12 - 9) ^ 2
      norm_num
  · -- Show for all z in set, z <= 81
    intro z h 
    rcases h with ⟨x, y, h1, h2, h3⟩
    rcases h2 with ⟨hx, hy⟩
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with ⟨hy1, hy2⟩
    nlinarith [sq_nonneg (x - 9), sq_nonneg (y - 9), sq_nonneg (x * y - 81), sq_nonneg ((12 - x) * (12 - y) - 9), h3, mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ y by linarith), mul_nonneg (show (0 : ℝ) ≤ (12 - x) by linarith) (show (0 : ℝ) ≤ (12 - y) by linarith)]