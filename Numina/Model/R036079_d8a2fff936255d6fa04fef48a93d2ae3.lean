import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_144137 {f : ℝ → ℝ}
  (hf : f = λ x => (sqrt (1 + x) + sqrt (1 - x) + 2) * (sqrt (1 - x ^ 2) + 1)) :
  IsLeast {y | ∃ x ∈ Icc 0 1, f x = y} (sqrt 2 + 2) := by
  constructor
  · -- Show that sqrt 2 + 2 is achievable at x = 1
    use 1
    constructor
    · -- Show that 1 ∈ [0, 1]
      exact ⟨by norm_num, by norm_num⟩
    · -- Show that f 1 = sqrt 2 + 2
      rw [hf]
      have h1 : sqrt (1 + (1 : ℝ)) = Real.sqrt 2 := by
        norm_num
      have h2 : sqrt (1 - (1 : ℝ)) = 0 := by
        rw [show (1 - (1 : ℝ)) = (0 : ℝ) by norm_num]
        simp
      have h3 : sqrt (1 - (1 : ℝ) ^ 2) = 0 := by
        rw [show (1 - (1 : ℝ) ^ 2) = (0 : ℝ) by norm_num]
        simp
      simp_all [h1, h2, h3]
      <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Show that sqrt 2 + 2 is the least value
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    rw [hf] at hfx
    simp at hfx
    have hx1 : 0 ≤ x := by
      have h : x ∈ Icc (0 : ℝ) 1 := hx
      exact h.1
    have hx2 : x ≤ 1 := by
      have h : x ∈ Icc (0 : ℝ) 1 := hx
      exact h.2
    have h1 : 0 ≤ (1 + x : ℝ) := by
      linarith
    have h2 : 0 ≤ (1 - x : ℝ) := by
      linarith
    have h3 : 0 ≤ (1 - x ^ 2 : ℝ) := by
      nlinarith [sq_nonneg (x - 1)]
    have h4 : sqrt (1 + x) + sqrt (1 - x) ≥ Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg (1 + x), Real.sqrt_nonneg (1 - x),
                  Real.sq_sqrt (show (0 : ℝ) ≤ (1 + x : ℝ) by linarith),
                  Real.sq_sqrt (show (0 : ℝ) ≤ (1 - x : ℝ) by linarith),
                  sq_nonneg (sqrt (1 + x) - sqrt (1 - x)),
                  Real.sqrt_nonneg (2 : ℝ),
                  Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
                  mul_nonneg (Real.sqrt_nonneg (1 + x)) (Real.sqrt_nonneg (1 - x)),
                  sq_nonneg (sqrt (1 + x) + sqrt (1 - x) - Real.sqrt 2),
                  Real.sqrt_nonneg (2),
                  Real.sq_sqrt (show (0 : ℝ) ≤ (1 + x : ℝ) by linarith),
                  Real.sq_sqrt (show (0 : ℝ) ≤ (1 - x : ℝ) by linarith)]
    nlinarith [Real.sqrt_nonneg (1 + x), Real.sqrt_nonneg (1 - x), Real.sqrt_nonneg (1 - x ^ 2),
                h4, Real.sqrt_nonneg (2 : ℝ),
                sq_nonneg (sqrt (1 + x) - sqrt (1 - x)), sq_nonneg (sqrt (1 - x ^ 2) - 0),
                Real.sq_sqrt (show (0 : ℝ) ≤ (1 + x : ℝ) by linarith),
                Real.sq_sqrt (show (0 : ℝ) ≤ (1 - x : ℝ) by linarith),
                Real.sq_sqrt (show (0 : ℝ) ≤ (1 - x ^ 2 : ℝ) by nlinarith),
                Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
                mul_nonneg (Real.sqrt_nonneg (1 + x)) (Real.sqrt_nonneg (1 - x)), Real.sqrt_nonneg 2]