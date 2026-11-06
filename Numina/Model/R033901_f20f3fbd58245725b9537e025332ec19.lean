import Mathlib
open Set

theorem algebra_9118 (m n : ℝ) (h : {x | x ^ 2 - m * x - 6 * n < 0} = {x | -3 < x ∧ x < 6}) :
    m + n = 6 := by
  -- Set f(x) = x^2 - mx - 6n
  let f x := x ^ 2 - m * x - 6 * n
  -- f is continuous
  have fcont : Continuous f := by continuity
  -- Rewrite the hypothesis h as f⁻¹'(-∞, 0) = (-3, 6)
  change f ⁻¹' (Iio 0) = Ioo (-3) 6 at h
  -- Use the lemma from topology: the frontier of the preimage of a continuous function
  -- is contained in the preimage of the frontier
  have h0 := Continuous.frontier_preimage_subset fcont (Iio 0)
  simp [h, show -3 < (6 : ℝ) by norm_num] at h0
  -- f(-3) = 0 and f(6) = 0
  have h1 : f (-3) = 0 := by
    apply h0
    simp
  have h2 : f 6 = 0 := by
    apply h0
    simp
  simp [f] at h1 h2
  nlinarith [sq_nonneg (m - 3: ℝ), sq_nonneg (n - 3: ℝ)]