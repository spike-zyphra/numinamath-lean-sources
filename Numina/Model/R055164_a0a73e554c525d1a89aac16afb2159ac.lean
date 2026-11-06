import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_194999 {f g : ℝ → ℝ}
  (hf : f '' (Icc (-8) 4) = Icc (-8) 4)
  (hg : g '' (Icc (-2) 6) = Icc (-2) 6) :
  IsGreatest {x | ∃ a b c d : ℝ, x = (a * b) - (c * d) ∧
    a ∈ Icc (-8) 4 ∧ b ∈ Icc (-2) 6 ∧ c ∈ Icc (-8) 4 ∧ d ∈ Icc (-2) 6} 72 := by
  constructor
  · -- Show 72 is in the set.
    use 4, 6, -8, 6
    constructor
    · -- Verify that 4 * 6 - (-8) * 6 = 72
      norm_num
    constructor
    · -- Show 4 ∈ [-8, 4]
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show 6 ∈ [-2, 6]
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show -8 ∈ [-8, 4]
      exact ⟨by norm_num, by norm_num⟩
    · -- Show 6 ∈ [-2, 6]
      exact ⟨by norm_num, by norm_num⟩
  
  · -- Show that for any element in the set, it cannot exceed 72.
    intro x hx
    rcases hx with ⟨a, b, c, d, h_eq, ha, hb, hc, hd⟩

    have h1 : -8 ≤ a := by
      have h1 : a ∈ Icc (-8) 4 := ha
      exact h1.left

    have h2 : a ≤ 4 := by
      have h2 : a ∈ Icc (-8) 4 := ha
      exact h2.right

    have h3 : -2 ≤ b := by
      have h3 : b ∈ Icc (-2) 6 := hb
      exact h3.left

    have h4 : b ≤ 6 := by
      have h4 : b ∈ Icc (-2) 6 := hb
      exact h4.right

    have h5 : -8 ≤ c := by
      have h5 : c ∈ Icc (-8) 4 := hc
      exact h5.left

    have h6 : c ≤ 4 := by
      have h6 : c ∈ Icc (-8) 4 := hc
      exact h6.right

    have h7 : -2 ≤ d := by
      have h7 : d ∈ Icc (-2) 6 := hd
      exact h7.left

    have h8 : d ≤ 6 := by
      have h8 : d ∈ Icc (-2) 6 := hd
      exact h8.right

    -- Now we need to show that (a * b) - (c * d) ≤ 72 given these constraints.
    nlinarith [sq_nonneg (a - 4), sq_nonneg (b - 6), sq_nonneg (c + 8), sq_nonneg (d - 6)]