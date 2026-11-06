import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_9337 (k : ℝ) :
(∃ x : ℝ, x ^ 2 + 4 * x + k = 0) ↔ k ≤ 4 := by
  constructor
  · -- Forward direction: if there exists a real root, then k ≤ 4
    rintro ⟨x, hx⟩
    have h : (x + 2) ^ 2 ≥ 0 := by
      apply sq_nonneg
    nlinarith
  · -- Backward direction: if k ≤ 4, then there exists a real root
    intro hk
    use -2 - Real.sqrt (4 - k)
    have h1 : Real.sqrt (4 - k) ≥ 0 := Real.sqrt_nonneg (4 - k)
    have h2 : (Real.sqrt (4 - k)) ^ 2 = 4 - k := Real.sq_sqrt (by linarith)
    nlinarith [h1, h2]