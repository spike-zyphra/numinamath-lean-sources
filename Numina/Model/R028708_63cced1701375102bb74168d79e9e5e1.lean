import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_304856 {f : ℝ → ℝ} (hf : ∀ x ∈ Icc (-3) 3, f x = (x + 1)*(x + 2)*(x + 3)*(x + 4) + 5) :
    IsLeast {y | ∃ x ∈ Icc (-3) 3, f x = y} 4 := by
  constructor
  · -- Show 4 is in the set
    use (-5 + Real.sqrt 5) / 2
    constructor
    · -- Show that $x \in Icc (-3) 3$
      constructor
      · -- Show that $-3 \leq (-5 + Real.sqrt 5) / 2$
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by linarith)]
      · -- Show that $(-5 + Real.sqrt 5) / 2 \leq 3$
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by linarith)]
    · -- Show that $f x = 4$
      have h1 : (-5 + Real.sqrt 5) / 2 ∈ Icc (-3 : ℝ) 3 := by
        constructor
        · -- Show that $-3 \leq (-5 + Real.sqrt 5) / 2$
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by linarith)]
        · -- Show that $(-5 + Real.sqrt 5) / 2 \leq 3$
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by linarith)]
      rw [hf ((-5 + Real.sqrt 5) / 2) h1]
      nlinarith [sq_nonneg (Real.sqrt 5), Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by linarith), sq_nonneg ((-5 + Real.sqrt 5) / 2 + 5 / 2), sq_nonneg ((-5 + Real.sqrt 5) / 2 + 4), sq_nonneg ((-5 + Real.sqrt 5) / 2 + 1), sq_nonneg ((-5 + Real.sqrt 5) / 2 + 2), sq_nonneg ((-5 + Real.sqrt 5) / 2 + 3)]
  · -- Show no value less than 4 is in the set
    intro y
    rintro ⟨x, hx, hfx⟩
    have hx1 : -3 ≤ x := by
      have h : x ∈ Icc (-3 : ℝ) 3 := hx
      exact h.1
    have hx2 : x ≤ 3 := by
      have h : x ∈ Icc (-3 : ℝ) 3 := hx
      exact h.2
    have hfx_eq : f x = (x + 1)*(x + 2)*(x + 3)*(x + 4) + 5 := by
      have h1 : x ∈ Icc (-3 : ℝ) 3 := hx
      specialize hf x h1
      simpa using hf
    rw [hfx_eq] at hfx
    nlinarith [sq_nonneg (x ^ 2 + 5 * x + 5), sq_nonneg (x + (5 - Real.sqrt 5) / 2), sq_nonneg (x + (5 + Real.sqrt 5) / 2), Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by linarith), sq_nonneg (x + 5 / 2), mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 5)]