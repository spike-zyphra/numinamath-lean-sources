import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_303827 (f : ℝ → ℝ → ℝ)
  (hf : f = λ x y => x * sqrt (1 - y) + y * sqrt (1 - x)) :
  IsGreatest {z | ∃ x y : ℝ, x ∈ Icc 0 1 ∧ y ∈ Icc 0 1 ∧ f x y = z} 1 := by 
  constructor
  · -- Show 1 is attainable
    use 1, 0
    constructor
    · -- Show 1 ∈ [0, 1]
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show 0 ∈ [0, 1]
      exact ⟨by norm_num, by norm_num⟩
    · -- Show f 1 0 = 1
      rw [hf]
      norm_num
  · -- Show that 1 is an upper bound
    intro z hz
    rcases hz with ⟨x, y, hx, hy, hfx⟩
    rw [hf] at hfx
    simp at hfx
    have h1 : 0 ≤ x := hx.left
    have h2 : x ≤ 1 := hx.right
    have h3 : 0 ≤ y := hy.left
    have h4 : y ≤ 1 := hy.right
    have h5 : sqrt (1 - y) ≤ 1 := by
      have h6 : 0 ≤ (1 - y : ℝ) := by linarith
      have h7 : sqrt (1 - y) ≤ sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h8 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
      linarith
    have h9 : sqrt (1 - x) ≤ 1 := by
      have h10 : 0 ≤ (1 - x : ℝ) := by linarith
      have h11 : sqrt (1 - x) ≤ sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h12 : sqrt (1 : ℝ) = 1 := Real.sqrt_one
      linarith
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), 
      sq_nonneg (sqrt (1 - y) - 1), 
      sq_nonneg (sqrt (1 - x) - 1), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 - y by linarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x by linarith), 
      hfx, 
      h1, h2, h3, h4
    ]