import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_324012 {f : ℝ → ℝ}
  (hf : f = λ x => (1 + x)^5 * (1 - x) * (1 - 2 * x)^2) :
  IsGreatest (image f (Icc (1 / 2) 1)) (f (7 / 8)) := by

  constructor
  · -- Prove that f(7/8) is in the image of f over [1/2, 1]
    rw [mem_image]
    use 7 / 8
    constructor
    · norm_num
    all_goals simp [hf]
    all_goals norm_num

  · -- Prove that f(7/8) is the greatest value in the image
    intro y hy
    rw [mem_image] at hy
    rcases hy with ⟨x, hx, hfx⟩

    have h1 : x ≥ 1 / 2 := by
      have h1 : x ∈ Icc (1 / 2 : ℝ) 1 := by
        simpa using hx
      exact h1.left
    have h2 : x ≤ 1 := by
      have h1 : x ∈ Icc (1 / 2 : ℝ) 1 := by
        simpa using hx
      exact h1.right

    simp [hf] at hfx ⊢
    
    have h3 : (1 + x) ^ 5 * (1 - x) * (1 - 2 * x) ^ 2 ≤ (1 + (7 / 8 : ℝ)) ^ 5 * (1 - (7 / 8 : ℝ)) * (1 - 2 * (7 / 8 : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg (x - 7 / 8), sq_nonneg ((x - 1 / 2) * (x - 7 / 8) * (x - 1)), sq_nonneg ((1 + x) * (x - 7 / 8) * (1 - 2 * x)), sq_nonneg ((1 - x) * (x - 7 / 8)), sq_nonneg ((1 - 2 * x) * (x - 7 / 8)), mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2), sq_nonneg (x - 7 / 8), sq_nonneg (x - 1 / 2), sq_nonneg (x - 1)]
    
    nlinarith