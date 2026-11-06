import Mathlib

open Real Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_225034 {z : ℂ} (hz : z = 1 / 2 + Complex.I * Real.sqrt 3 / 2) :
    ∑ k ∈ range 2010, z ^ (k + 1) = 0 := by

  have h1 : z^3 = -1 := by
    rw [hz]
    simp [pow_three, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, mul_add, add_mul]
    field_simp
    <;> ring_nf <;> norm_num
  have h2 : z^2010 = 1 := by
    calc
      z^2010 = (z^3)^670 := by ring_nf
      _ = (-1)^670 := by rw [h1]
      _ = (1 : ℂ) := by norm_num

  have h3 : ∀ n, ∑ k ∈ range n, z ^ (k + 1) = z * (1 - z^ n) / (1 - z) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      field_simp [(show (1 - z : ℂ) ≠ 0 by
        by_contra h
        have h3' : z = 1 := by
          have h4' : 1 - z = 0 := by
            simpa using h
          have h5' : z = 1 := by
            calc
              z = 1 - (1 - z) := by ring_nf
              _ = 1 - 0 := by rw [h4']
              _ = 1 := by ring_nf
          exact h5'
        rw [hz] at h3'
        have h4 : (1 / 2 + Complex.I * Real.sqrt 3 / 2 : ℂ) = (1 : ℂ) := h3'
        have h5 : (1 / 2 + Complex.I * Real.sqrt 3 / 2 : ℂ).re = (1 : ℂ).re := by
          rw [h4]
        norm_num at h5
        all_goals
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      )]
      <;> ring_nf

  have h4 : z * (1 - z^2010) / (1 - z) = 0 := by
    rw [h2]
    norm_num

  have h5 : ∑ k ∈ range 2010, z ^ (k + 1) = z * (1 - z^2010) / (1 - z) := by
    apply h3
  rw [h5]
  exact h4