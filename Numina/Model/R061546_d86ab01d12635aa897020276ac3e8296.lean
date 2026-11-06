import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_194901 :
  IsGreatest {x | ∃ a b c d : ℝ, x = a + 2*b + c + 2*d - a*b - b*c - c*d - d*a ∧
    a ∈ Icc (-5.5) 5.5 ∧ b ∈ Icc (-5.5) 5.5 ∧ c ∈ Icc (-5.5) 5.5 ∧ d ∈ Icc (-5.5) 5.5} 132 := by
  constructor
  · -- Show 132 is achievable
    use -5.5, 5.5, -5.5, 5.5
    norm_num [mem_Icc]
  · -- Now show that it's the greatest
    rintro x ⟨a, b, c, d, h_eq, ha, hb, hc, hd⟩
    rw [h_eq]
    have ha1 : -5.5 ≤ a := by
      exact ha.left
    have ha2 : a ≤ 5.5 := by
      exact ha.right
    have hb1 : -5.5 ≤ b := by
      exact hb.left
    have hb2 : b ≤ 5.5 := by
      exact hb.right
    have hc1 : -5.5 ≤ c := by
      exact hc.left
    have hc2 : c ≤ 5.5 := by
      exact hc.right
    have hd1 : -5.5 ≤ d := by
      exact hd.left
    have hd2 : d ≤ 5.5 := by
      exact hd.right
    nlinarith [sq_nonneg (a + c + 11), sq_nonneg (b + d - 11), 
      mul_nonneg (show (0 : ℝ) ≤ 5.5 + a by linarith) (show (0 : ℝ) ≤ 5.5 + c by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 5.5 + b by linarith) (show (0 : ℝ) ≤ 5.5 + d by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 5.5 - a by linarith) (show (0 : ℝ) ≤ 5.5 - c by linarith),
      mul_nonneg (show (0 : ℝ) ≤ 5.5 - b by linarith) (show (0 : ℝ) ≤ 5.5 - d by linarith)]