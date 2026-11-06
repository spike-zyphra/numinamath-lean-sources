import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_170090 :
  IsGreatest {x : ℝ | ∃ a b c d : ℝ, x = a + b + c + d - a * b - b * c - c * d - d * a ∧
    a ∈ Icc 0 1 ∧ b ∈ Icc 0 1 ∧ c ∈ Icc 0 1 ∧ d ∈ Icc 0 1} 2 := by
  constructor
  · -- Show that 2 is achievable
    use 0, 1, 0, 1
    norm_num [mem_Icc]
  · -- Show that any value in the set is ≤ 2
    rintro x ⟨a, b, c, d, heq, ha, hb, hc, hd⟩
    rcases mem_Icc.mp ha with ⟨ha0, ha1⟩
    rcases mem_Icc.mp hb with ⟨hb0, hb1⟩
    rcases mem_Icc.mp hc with ⟨hc0, hc1⟩
    rcases mem_Icc.mp hd with ⟨hd0, hd1⟩
    nlinarith [sq_nonneg (a - c), sq_nonneg (b - d), 
      sq_nonneg (a - 1/2), sq_nonneg (b - 1/2), 
      sq_nonneg (c - 1/2), sq_nonneg (d - 1/2),
      mul_nonneg (show (0 : ℝ) ≤ 1 - a by linarith) (show (0 : ℝ) ≤ 1 - b by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 1 - a by linarith) (show (0 : ℝ) ≤ 1 - c by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 1 - a by linarith) (show (0 : ℝ) ≤ 1 - d by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 1 - b by linarith) (show (0 : ℝ) ≤ 1 - c by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 1 - b by linarith) (show (0 : ℝ) ≤ 1 - d by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 1 - c by linarith) (show (0 : ℝ) ≤ 1 - d by linarith),
      mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith),
      mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ c by linarith),
      mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ d by linarith),
      mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ c by linarith),
      mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ d by linarith),
      mul_nonneg (show (0 : ℝ) ≤ c by linarith) (show (0 : ℝ) ≤ d by linarith)
    ]