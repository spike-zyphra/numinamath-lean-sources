import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_194813 :
  IsGreatest {x | ∃ a b c d : ℝ, x = a + 2*b + c + 2*d - a*b - b*c - c*d - d*a ∧
    a ∈ Icc (-4.5) 4.5 ∧ b ∈ Icc (-4.5) 4.5 ∧ c ∈ Icc (-4.5) 4.5 ∧ d ∈ Icc (-4.5) 4.5} 90 := by
  constructor
  · -- Show 90 can be achieved.
    use -4.5, 4.5, -4.5, 4.5
    norm_num [mem_Icc]
  · -- Show no value greater than 90 can be achieved.
    intro x hx
    rcases hx with ⟨a, b, c, d, h_eq, ha, hb, hc, hd⟩
    rw [mem_Icc] at ha hb hc hd
    have h1 : -4.5 ≤ a := by linarith [ha.1]
    have h2 : a ≤ 4.5 := by linarith [ha.2]
    have h1b : -4.5 ≤ b := by linarith [hb.1]
    have h2b : b ≤ 4.5 := by linarith [hb.2]
    have h1c : -4.5 ≤ c := by linarith [hc.1]
    have h2c : c ≤ 4.5 := by linarith [hc.2]
    have h1d : -4.5 ≤ d := by linarith [hd.1]
    have h2d : d ≤ 4.5 := by linarith [hd.2]
    nlinarith [sq_nonneg (a + 4.5), sq_nonneg (b - 4.5), sq_nonneg (c + 4.5), sq_nonneg (d - 4.5), 
          mul_nonneg (show 0 ≤ (4.5 + a) by linarith) (show 0 ≤ (4.5 - a) by linarith),
          mul_nonneg (show 0 ≤ (4.5 + b) by linarith) (show 0 ≤ (4.5 - b) by linarith),
          mul_nonneg (show 0 ≤ (4.5 + c) by linarith) (show 0 ≤ (4.5 - c) by linarith),
          mul_nonneg (show 0 ≤ (4.5 + d) by linarith) (show 0 ≤ (4.5 - d) by linarith)]