import Mathlib

open Real Set
open scoped Real

theorem inequalities_166775 (x : ℝ) (hx : x ∈ Icc (π/4) (π/2)) :
    8 * cos x ^ 2 * (1 - 1 / tan x) < 1 := by
  rw [mem_Icc] at hx
  have h1 : π / 4 ≤ x := hx.1
  have h2 : x ≤ π / 2 := hx.2

  have htan : tan x = sin x / cos x := by rw [tan_eq_sin_div_cos]

  rw [htan]

  have hs : sin x > 0 := by
    have hp1 : x > 0 := by linarith [Real.pi_pos, h1, h2]
    have hp2 : x < Real.pi := by
      nlinarith [Real.pi_pos, h1, h2]
    apply sin_pos_of_pos_of_lt_pi hp1 hp2

  have hc : cos x ≥ 0 := by
    apply cos_nonneg_of_mem_Icc
    constructor
    · -- Show $-π/2 ≤ x$
      nlinarith [Real.pi_pos, h1, h2]
    · -- Show $x ≤ π/2$
      linarith [Real.pi_pos, h1, h2]

  have h4 : sin x > 0 := hs
  have h3 : cos x ≥ 0 := hc

  have h6 : 8 * cos x ^ 2 * (1 - 1 / (sin x / cos x)) - (1 : ℝ) < 0 := by
    have h16 : sin x > 0 := hs
    have h18 : cos x ≥ 0 := hc
    have h5 : 8 * cos x ^ 2 * (1 - 1 / (sin x / cos x)) - (1 : ℝ) =
      (8 * cos x ^ 2 * (sin x - cos x) - sin x) / sin x := by
      field_simp [h16, h18]
      <;> ring
    rw [h5]
    have h6 : 8 * cos x ^ 2 * (sin x - cos x) - sin x < 0 := by
      nlinarith [Real.pi_pos, Real.cos_pi_div_two, Real.sin_pi_div_two,
          Real.cos_pi_div_four, Real.sin_pi_div_four,
          sq_nonneg (cos x - sin x), sq_nonneg (cos x - 1 / 2), sq_nonneg (sin x - 1 / 2),
          h16, h18,
          Real.cos_sq_add_sin_sq x,
          mul_nonneg (show (0 : ℝ) ≤ cos x by linarith) (show (0 : ℝ) ≤ sin x by linarith)
        ]
    apply div_neg_of_neg_of_pos h6 h16

  linarith