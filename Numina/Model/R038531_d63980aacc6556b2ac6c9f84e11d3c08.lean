import Mathlib

open Real Set
open scoped Real

theorem algebra_197543 {x : ℝ} (hx : 0 ≤ x ∧ x ≤ π/2)
    (h : sqrt (sin x + 1) - sqrt (1 - sin x) = sin (x/2)) :
    tan x = 0 := by
  have h1 : 0 ≤ x := hx.1
  have h2 : x ≤ π / 2 := hx.2
  have h3 : 0 ≤ sin x := by
    apply sin_nonneg_of_nonneg_of_le_pi
    linarith
    linarith
  have h4 : sin x ≤ 1 := by
    have h5 : sin x ≤ sin (π / 2) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      all_goals linarith
    rw [show sin (π / 2) = 1 by rw [sin_pi_div_two]] at h5
    linarith
  have h5 : 0 ≤ sin x + 1 := by linarith
  have h6 : 0 ≤ 1 - sin x := by linarith
  have hcos : 0 ≤ cos x := by
    apply cos_nonneg_of_mem_Icc
    constructor
    linarith [Real.pi_pos, h1, h2]
    linarith [Real.pi_pos, h1, h2]
  have h7 : sin (x / 2) ≥ 0 := by
    apply sin_nonneg_of_nonneg_of_le_pi
    linarith [Real.pi_pos, h1]
    linarith [Real.pi_pos, h2]
  have eq1 : sqrt (sin x + 1) - sqrt (1 - sin x) = sin (x / 2) := h
  have eq2 : (sqrt (sin x + 1) - sqrt (1 - sin x)) ^ 2 = sin (x / 2) ^ 2 := by
    rw [eq1]
  have eq3 : (sqrt (sin x + 1) - sqrt (1 - sin x)) ^ 2 = (sqrt (sin x + 1)) ^ 2 + (sqrt (1 - sin x)) ^ 2 - 2 * (sqrt (sin x + 1) * sqrt (1 - sin x)) := by
    ring
  have eq4 : sin (x / 2) ^ 2 = (1 - cos x)/2 := by
    have h9 : sin (x / 2) ^ 2 = (1 - cos x)/2 := by
      rw [sin_sq_eq_half_sub]
      <;> ring_nf <;> field_simp [Real.cos_sq]
      <;> nlinarith [Real.cos_sq_add_sin_sq x]
    linarith
  rw [eq3, eq4] at eq2
  have eq5 : (sqrt (sin x + 1)) ^ 2 = sin x + 1 := by
    rw [Real.sq_sqrt]
    linarith
  have eq6 : (sqrt (1 - sin x)) ^ 2 = 1 - sin x := by
    rw [Real.sq_sqrt]
    linarith
  have eq7 : (sqrt (sin x + 1)) * (sqrt (1 - sin x)) = cos x := by
    calc
      sqrt (sin x + 1) * sqrt (1 - sin x)
        = sqrt ((sin x + 1) * (1 - sin x)) := by
          rw [← Real.sqrt_mul (by linarith)]
      _ = sqrt (1 - sin x ^ 2) := by
        ring_nf
      _ = sqrt (cos x ^ 2) := by
        rw [show 1 - sin x ^ 2 = cos x ^ 2 by
          have h : sin x ^ 2 + cos x ^ 2 = 1 := by
            exact Real.sin_sq_add_cos_sq x
          linarith]
      _ = cos x := by
        rw [Real.sqrt_sq (show 0 ≤ cos x by linarith)]
  rw [eq5, eq6, eq7] at eq2
  have h8 : cos x = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq x, h3, h4, hcos]
  have h9 : x = 0 := by
    have h10 : cos x = 1 := h8
    have h10' : cos x = 1 := h10
    have h11 : x = 0 := by
      have h12 : x ≥ 0 := by linarith
      have h13 : x ≤ π / 2 := by linarith
      have h14 : cos x = 1 := h10'
      by_cases h15 : x > 0
      · have h16 : cos x < 1 := by
          have h17 : cos x < cos (0 : ℝ) := by
            apply Real.cos_lt_cos_of_nonneg_of_le_pi
            all_goals
              linarith [Real.pi_pos, h15]
          have h18 : cos (0 : ℝ) = 1 := by
            rw [cos_zero]
          linarith [h18, h17]
        linarith [h16, h14]
      linarith
    linarith
  rw [h9]
  simp