import Mathlib

open Real Set

theorem inequalities_191212 :
    IsLeast {u + v + w | (u : ℝ) (v : ℝ) (w : ℝ) (_ : 0 < u) (_ : 0 < v) (_ : 0 < w)
    (_ : 1 ≤ u * √ (v * w) + v * √ (w * u) + w * √(u * v))} √3 := by
  constructor
  · -- First, prove that √3 is in the set.
    use Real.sqrt 3 / 3, Real.sqrt 3 / 3, Real.sqrt 3 / 3
    have h1 : 0 < Real.sqrt 3 / 3 := by
      have h2 : 0 < Real.sqrt 3 := by
        positivity
      linarith
    have h14 : 1 ≤ (Real.sqrt 3 / 3) * Real.sqrt ((Real.sqrt 3 / 3) * (Real.sqrt 3 / 3)) + (Real.sqrt 3 / 3) * Real.sqrt ((Real.sqrt 3 / 3) * (Real.sqrt 3 / 3)) + (Real.sqrt 3 / 3) * Real.sqrt ((Real.sqrt 3 / 3) * (Real.sqrt 3 / 3)) := by
      have h15 : Real.sqrt ((Real.sqrt 3 / 3) * (Real.sqrt 3 / 3)) = Real.sqrt 3 / 3 := by
        have h17 : (Real.sqrt 3 / 3 : ℝ) * (Real.sqrt 3 / 3 : ℝ) = (1 / 3 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        have h18 : Real.sqrt ((1 / 3 : ℝ)) = Real.sqrt 3 / 3 := by
          rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          <;> ring_nf <;> norm_num
        rw [h17] at *
        linarith [h18]
      rw [h15] at *
      nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h19 : Real.sqrt 3 / 3 + Real.sqrt 3 / 3 + Real.sqrt 3 / 3 = Real.sqrt 3 := by
      linarith
    simp [h1, h14, h19]
  · -- Now, prove that √3 is the minimum element.
    rintro x ⟨u, v, w, hu, hv, hw, h, rfl⟩
    have h1 : 1 ≤ u * Real.sqrt (v * w) + v * Real.sqrt (w * u) + w * Real.sqrt (u * v) := h
    have h2 : Real.sqrt (v * w) = Real.sqrt v * Real.sqrt w := by
      rw [Real.sqrt_mul (by positivity)]
    have h3 : Real.sqrt (w * u) = Real.sqrt w * Real.sqrt u := by
      rw [Real.sqrt_mul (by positivity)]
    have h4 : Real.sqrt (u * v) = Real.sqrt u * Real.sqrt v := by
      rw [Real.sqrt_mul (by positivity)]
    rw [h2, h3, h4] at h1
    have h5 : Real.sqrt u ≥ 0 := by positivity
    have h6 : Real.sqrt v ≥ 0 := by positivity
    have h7 : Real.sqrt w ≥ 0 := by positivity
    have h8 : Real.sqrt u ^ 2 = u := by
      rw [Real.sq_sqrt]
      positivity
    have h9 : Real.sqrt v ^ 2 = v := by
      rw [Real.sq_sqrt]
      positivity
    have h10 : Real.sqrt w ^ 2 = w := by
      rw [Real.sq_sqrt]
      positivity
    have h11 : (u + v + w) ^ 2 ≥ 3 := by
      nlinarith [sq_nonneg (Real.sqrt u - Real.sqrt v), sq_nonneg (Real.sqrt v - Real.sqrt w), sq_nonneg (Real.sqrt w - Real.sqrt u),
        sq_nonneg (Real.sqrt u * Real.sqrt v - Real.sqrt v * Real.sqrt w), sq_nonneg (Real.sqrt v * Real.sqrt w - Real.sqrt w * Real.sqrt u), sq_nonneg (Real.sqrt w * Real.sqrt u - Real.sqrt u * Real.sqrt v),
        mul_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg v), mul_nonneg (Real.sqrt_nonneg v) (Real.sqrt_nonneg w), mul_nonneg (Real.sqrt_nonneg w) (Real.sqrt_nonneg u)]
    have h12 : (u + v + w) ≥ Real.sqrt 3 := by
      have h31 : Real.sqrt 3 ^ 2 = 3 := by
        rw [Real.sq_sqrt]
        positivity
      have h30 : (u + v + w) ≥ 0 := by positivity
      have h33 : Real.sqrt 3 ≥ 0 := by positivity
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg ((u + v + w) ^ 2 - 3)]
    linarith