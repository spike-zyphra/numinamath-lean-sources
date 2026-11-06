import Mathlib

theorem algebra_599997 (f : ℝ → ℝ) (hf : f = fun x => 3 * Real.sqrt (x - 1) + Real.sqrt (35 - 7 * x)) :
    IsGreatest (Set.image f {x | 1 ≤ x ∧ x ≤ 5}) 8 := by
  constructor
  · -- Show 8 is in the image
    rw [Set.mem_image]
    use 3.25
    constructor
    · -- Show 3.25 is in the domain
      norm_num
    · -- Show f(3.25) = 8
      rw [hf]
      have h1 : Real.sqrt (3.25 - 1 : ℝ) = 1.5 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : Real.sqrt (35 - 7 * (3.25 : ℝ)) = 3.5 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      simp only [h1, h2]
      all_goals norm_num
  · -- Show that 8 is the greatest
    intro y hy
    rw [Set.mem_image] at hy
    rcases hy with ⟨x, hx, hy⟩
    have h1 : 1 ≤ x := hx.1
    have h2 : x ≤ 5 := hx.2
    rw [hf] at hy
    have h3 : 0 ≤ x - 1 := by linarith
    have h4 : 0 ≤ 35 - 7 * x := by nlinarith
    simp at hy
    -- Show $f(x) \leq 8$ for all $x \in [1,5]$
    have h5 : (3 * Real.sqrt (x - 1) + Real.sqrt (35 - 7 * x)) ^ 2 ≤ 64 := by
      nlinarith [sq_nonneg (3 * Real.sqrt (x - 1) - Real.sqrt (35 - 7 * x) * 3 / 2),
        sq_nonneg (Real.sqrt (x - 1) - Real.sqrt (35 - 7 * x) * 7 / 6),
        Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (35 - 7 * x),
        mul_nonneg (Real.sqrt_nonneg (x - 1)) (Real.sqrt_nonneg (35 - 7 * x)),
        Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith),
        Real.sq_sqrt (show (0 : ℝ) ≤ (35 - 7 * x : ℝ) by nlinarith),
        sq_nonneg (x - 3.25)]
    have h6 : 3 * Real.sqrt (x - 1) + Real.sqrt (35 - 7 * x) ≤ 8 := by
      nlinarith [Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (35 - 7 * x),
        h5, sq_nonneg (3 * Real.sqrt (x - 1) + Real.sqrt (35 - 7 * x) - 8)]
    linarith [h6, hy]