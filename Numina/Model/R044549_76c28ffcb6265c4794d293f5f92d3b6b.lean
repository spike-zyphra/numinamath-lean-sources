import Mathlib

open Real

theorem inequalities_230072
  : IsLeast
    ((fun (u, v, w) => u + v + w) '' {(u, v, w) : ℝ × ℝ × ℝ | 0 < u ∧ 0 < v ∧ 0 < w ∧ 1 ≤ u * √(v * w) + v * √(w * u) + w * √(u * v)})
    √3
  := by
  constructor
  · -- First direction: show that √3 is achieved
    use (Real.sqrt 3 / 3, Real.sqrt 3 / 3, Real.sqrt 3 / 3)
    constructor
    · -- Show √3 in range
      have h1 : Real.sqrt 3 / 3 > 0 := by
        have h2 : Real.sqrt 3 > 0 := by positivity
        linarith
      exact ⟨h1, h1, h1, by
        have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
        have h4 : (Real.sqrt 3 / 3 : ℝ) * Real.sqrt ((Real.sqrt 3 / 3) * (Real.sqrt 3 / 3)) + (Real.sqrt 3 / 3 : ℝ) * Real.sqrt ((Real.sqrt 3 / 3) * (Real.sqrt 3 / 3)) + (Real.sqrt 3 / 3 : ℝ) * Real.sqrt ((Real.sqrt 3 / 3) * (Real.sqrt 3 / 3)) = 1 := by
          have h5 : Real.sqrt ((Real.sqrt 3 / 3) * (Real.sqrt 3 / 3)) = Real.sqrt 3 / 3 := by
            have h6 : (Real.sqrt 3 / 3 : ℝ) * (Real.sqrt 3 / 3 : ℝ) = (3 / 9 : ℝ) := by
              nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
            rw [h6]
            have h7 : Real.sqrt ((3 / 9 : ℝ)) = Real.sqrt 3 / 3 := by
              rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
              <;> ring_nf <;> norm_num
            exact h7
          rw [h5]
          nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
        linarith
      ⟩
    · -- Show minimality
      have h12 : (Real.sqrt 3 / 3 + Real.sqrt 3 / 3 + Real.sqrt 3 / 3 : ℝ) = Real.sqrt 3 := by
        linarith
      simp_all [Prod.ext_iff]
  · -- Now the minimality
    intro a ha
    rcases ha with ⟨⟨u, v, w⟩, ⟨hu, hv, hw, h1⟩, h2⟩
    have h9 : u + v + w ≥ Real.sqrt 3 := by
      by_contra h
      push_neg at h
      have h5 : u * Real.sqrt (v * w) + v * Real.sqrt (w * u) + w * Real.sqrt (u * v) < (1 : ℝ) := by
        have h14 : u * Real.sqrt (v * w) + v * Real.sqrt (w * u) + w * Real.sqrt (u * v) ≤ (u + v + w) ^ 2 / 3 := by
          have h8 : Real.sqrt (v * w) ≤ (v + w) / 2 := by
            have h11 : Real.sqrt (v * w) = Real.sqrt v * Real.sqrt w := by
              rw [Real.sqrt_mul (by positivity)]
            nlinarith [sq_nonneg (Real.sqrt v - Real.sqrt w), Real.sq_sqrt (show 0 ≤ (v : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (w : ℝ) by linarith), Real.sqrt_nonneg v, Real.sqrt_nonneg w]
          have h9 : Real.sqrt (w * u) ≤ (w + u) / 2 := by
            have h11 : Real.sqrt (w * u) = Real.sqrt w * Real.sqrt u := by
              rw [Real.sqrt_mul (by positivity)]
            nlinarith [sq_nonneg (Real.sqrt w - Real.sqrt u), Real.sq_sqrt (show 0 ≤ (w : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (u : ℝ) by linarith), Real.sqrt_nonneg w, Real.sqrt_nonneg u]
          have h10 : Real.sqrt (u * v) ≤ (u + v) / 2 := by
            have h11 : Real.sqrt (u * v) = Real.sqrt u * Real.sqrt v := by
              rw [Real.sqrt_mul (by positivity)]
            nlinarith [sq_nonneg (Real.sqrt u - Real.sqrt v), Real.sq_sqrt (show 0 ≤ (u : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (v : ℝ) by linarith), Real.sqrt_nonneg u, Real.sqrt_nonneg v]
          nlinarith [sq_nonneg (u - v), sq_nonneg (u - w), sq_nonneg (v - w),
            mul_nonneg (show 0 ≤ (u : ℝ) by linarith) (show 0 ≤ (v : ℝ) by linarith),
            mul_nonneg (show 0 ≤ (u : ℝ) by linarith) (show 0 ≤ (w : ℝ) by linarith),
            mul_nonneg (show 0 ≤ (v : ℝ) by linarith) (show 0 ≤ (w : ℝ) by linarith)
          ]
        have h6 : (u + v + w) ^ 2 / 3 < (1 : ℝ) := by
          have h4 : (u + v + w) < Real.sqrt 3 := by linarith
          have h7 : (u + v + w) ^ 2 < (3 : ℝ) := by
            have h8 : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith)
            nlinarith [h4, Real.sqrt_nonneg 3]
          linarith [h7]
        nlinarith
      linarith
    have h13 : a = u + v + w := by
      simp at h2 ⊢
      linarith
    nlinarith