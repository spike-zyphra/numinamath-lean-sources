import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_15699 (f : ℝ → ℝ) (hf : f = λ x => 3 * x - x ^ 3)
  (I : Set ℝ) (hI : I = Icc 0 (Real.sqrt 3)) :
  IsGreatest (image f I) 2 := by
  constructor
  · -- Show that 2 belongs to the image of f over I
    rw [mem_image]
    rw [hI]
    use 1
    -- We need to prove that 1 ∈ [0, √3] and f(1) = 2
    constructor
    · -- Show that 1 belongs to [0, sqrt 3]
      have h1sqrt3 : 1 ≤ Real.sqrt 3 := by
        have h1 : (1 : ℝ) ^ 2 ≤ (3 : ℝ) := by norm_num
        have h2 : (1 : ℝ) ≤ Real.sqrt 3 := by
          apply Real.le_sqrt_of_sq_le
          all_goals nlinarith
        linarith
      constructor
      · -- Show that 0 ≤ 1
        norm_num
      · -- Show that 1 ≤ sqrt 3
        linarith [Real.sqrt_nonneg 3, h1sqrt3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    · -- Show that f(1) = 2
      norm_num [hf]
  · -- Show that 2 is an upper bound for the image
    intro y hy
    rw [hI] at hy
    rw [mem_image] at hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx0 : 0 ≤ x := by
      have h : x ∈ Icc (0 : ℝ) (Real.sqrt 3) := hx
      exact h.left
    have hx1 : x ≤ Real.sqrt 3 := by
      have h : x ∈ Icc (0 : ℝ) (Real.sqrt 3) := hx
      exact h.right
    have h2 : -x ^ 3 + 3 * x - 2 ≤ 0 := by
      nlinarith [sq_nonneg ((x - 1) : ℝ), sq_nonneg ((x + 2) : ℝ),
        sq_nonneg ((x - Real.sqrt 3) : ℝ), sq_nonneg (x : ℝ),
        Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
        mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3), sq_nonneg (x^2 : ℝ)]
    simp only [hf]
    all_goals
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (x^2), sq_nonneg (x - 1), sq_nonneg (x + 2), sq_nonneg (x - Real.sqrt 3), sq_nonneg (x * (x - 1)), sq_nonneg ((x - 1) * (x - Real.sqrt 3))]