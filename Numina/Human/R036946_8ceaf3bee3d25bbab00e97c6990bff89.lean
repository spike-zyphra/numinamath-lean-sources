import Mathlib

open Real Set
open scoped BigOperators

/- The slope of the tangent line at a point on the graph of the function $f(x)=x+\cos x-\sqrt{3}\sin x$ is $k$. The range of values for $k$ is ___          ___. -/
theorem calculus_12747 (f : ℝ → ℝ) (hf : f = λ x => x + cos x - sqrt 3 * sin x)
  (k : ℝ) :
  k ∈ Icc (-1) 3 ↔ ∃ x, deriv f x = k := by
  constructor
  · -- Assume k ∈ [-1, 3]
    intro hk
    rcases hk with ⟨hk1, hk2⟩
    use arcsin ((1 - k) / 2) - Real.pi / 3
    rw [hf]
    simp [deriv_add, deriv_sub, deriv_id'', differentiableAt_cos, differentiableAt_sin, mul_comm]
    have h1 : -1 ≤ (1 - k) / 2 := by linarith
    have h2 : (1 - k) / 2 ≤ 1 := by linarith
    have h3 : sin (arcsin ((1 - k) / 2)) = (1 - k) / 2 := by
      apply sin_arcsin h1 h2
    have h4 : cos (arcsin ((1 - k) / 2)) = Real.sqrt (1 - ((1 - k) / 2) ^ 2) := by
      rw [Real.cos_arcsin]
    have h5 : sin (arcsin ((1 - k) / 2) - Real.pi / 3) = (1 - k) / 2 * (1 / 2) - Real.sqrt (1 - ((1 - k) / 2) ^ 2) * (Real.sqrt 3 / 2) := by
      rw [sin_sub]
      rw [h3]
      rw [h4]
      have h6 : cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
      have h7 : sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
      simp [h6, h7]
    have h6 : cos (arcsin ((1 - k) / 2) - Real.pi / 3) = Real.sqrt (1 - ((1 - k) / 2) ^ 2) * (1 / 2) + (1 - k) / 2 * (Real.sqrt 3 / 2) := by
      rw [cos_sub]
      rw [h4]
      rw [h3]
      have h7 : cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
      have h8 : sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
      simp [h7, h8]
    have h7 : 1 - sin (arcsin ((1 - k) / 2) - Real.pi / 3) - Real.sqrt 3 * cos (arcsin ((1 - k) / 2) - Real.pi / 3) = k := by
      rw [h5, h6]
      have h8 : Real.sqrt 3 * Real.sqrt 3 = 3 := by
        calc
          Real.sqrt 3 * Real.sqrt 3 = (Real.sqrt 3) ^ 2 := by ring
          _ = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
      nlinarith [Real.sq_sqrt (show 0 ≤ (1 - ((1 - k) / 2) ^ 2) by nlinarith [sq_nonneg (1 - k), sq_nonneg (Real.sqrt 3)])]
    linarith [h7]
  · -- Assume there exists x such that f'(x) = k
    rintro ⟨x, hx⟩
    rw [hf] at hx
    simp [deriv_add, deriv_sub, deriv_id'', differentiableAt_cos, differentiableAt_sin, mul_comm] at hx
    have h1 : -1 ≤ k := by
      have h2 : Real.sin x + Real.sqrt 3 * Real.cos x ≤ 2 := by
        have h3 : Real.sin x + Real.sqrt 3 * Real.cos x = 2 * Real.sin (x + Real.pi / 3) := by
          rw [Real.sin_add]
          have h4 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
          have h5 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
          rw [h4, h5]
          ring
        rw [h3]
        have h4 : Real.sin (x + Real.pi / 3) ≤ 1 := Real.sin_le_one (x + Real.pi / 3)
        linarith
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (Real.sin x), sq_nonneg (Real.cos x), h2]
    have h2 : k ≤ 3 := by
      have h3 : Real.sin x + Real.sqrt 3 * Real.cos x ≥ -2 := by
        have h4 : Real.sin x + Real.sqrt 3 * Real.cos x = 2 * Real.sin (x + Real.pi / 3) := by
          rw [Real.sin_add]
          have h5 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
          have h6 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
          rw [h5, h6]
          ring
        rw [h4]
        have h5 : -1 ≤ Real.sin (x + Real.pi / 3) := by linarith [Real.neg_one_le_sin (x + Real.pi / 3)]
        linarith
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (Real.sin x), sq_nonneg (Real.cos x), h3]
    exact ⟨h1, h2⟩