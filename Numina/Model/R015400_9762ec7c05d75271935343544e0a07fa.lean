import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_197251 :
  IsGreatest {x | ∃ a b c d : ℝ, x = a + 2 * b + c + 2 * d - a * b - b * c - c * d - d * a ∧
    a ∈ Icc (-5.5) 5.5 ∧ b ∈ Icc (-5.5) 5.5 ∧ c ∈ Icc (-5.5) 5.5 ∧ d ∈ Icc (-5.5) 5.5} 132 := by
  constructor
  · -- Show that 132 is in the set
    use -5.5, 5.5, -5.5, 5.5
    norm_num [mem_Icc]
  · -- Show that 132 is the greatest
    intro x h
    rcases h with ⟨a, b, c, d, h_eq, ha, hb, hc, hd⟩
    rw [mem_Icc] at ha hb hc hd
    have h1 : -5.5 ≤ a := by linarith [ha.1]
    have h2 : a ≤ 5.5 := by linarith [ha.2]
    have h3 : -5.5 ≤ b := by linarith [hb.1]
    have h4 : b ≤ 5.5 := by linarith [hb.2]
    have h5 : -5.5 ≤ c := by linarith [hc.1]
    have h6 : c ≤ 5.5 := by linarith [hc.2]
    have h7 : -5.5 ≤ d := by linarith [hd.1]
    have h8 : d ≤ 5.5 := by linarith [hd.2]
    nlinarith [sq_nonneg (a + c + 11), sq_nonneg (b + d - 11), sq_nonneg (a + 5.5), sq_nonneg (c + 5.5), sq_nonneg (b - 5.5), sq_nonneg (d - 5.5), mul_nonneg (show (0 : ℝ) ≤ 5.5 + a by linarith) (show (0 : ℝ) ≤ 5.5 - a by linarith), mul_nonneg (show (0 : ℝ) ≤ 5.5 + b by linarith) (show (0 : ℝ) ≤ 5.5 - b by linarith), mul_nonneg (show (0 : ℝ) ≤ 5.5 + c by linarith) (show (0 : ℝ) ≤ 5.5 - c by linarith), mul_nonneg (show (0 : ℝ) ≤ 5.5 + d by linarith) (show (0 : ℝ) ≤ 5.5 - d by linarith)]