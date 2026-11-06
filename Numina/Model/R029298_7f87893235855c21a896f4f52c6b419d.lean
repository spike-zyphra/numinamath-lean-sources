import Mathlib

open Real Set
open scoped Real

theorem calculus_15225 {θ : ℝ} (hθ : θ ∈ Ioo 0 (π / 2)) :
    sqrt 2 * sin (π / 18) = cos θ - sin θ ↔ θ * 180 / π = 35 := by
  rcases hθ with ⟨hθ1, hθ2⟩
  constructor
  · -- Forward direction: if sqrt 2 * sin (π / 18) = cos θ - sin θ then θ * 180 / π = 35
    intro h_eq
    have h : cos θ - sin θ = sqrt 2 * cos (θ + Real.pi / 4) := by
      rw [Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four]
      ring_nf
      <;> field_simp [Real.sqrt_pos.mpr, Real.sqrt_mul_self]
      <;> ring_nf
      <;> simp [mul_add, sub_eq_add_neg, mul_neg, neg_mul]
      <;> ring
    rw [h] at h_eq
    have h2 : sin (Real.pi / 18) = cos (θ + Real.pi / 4) := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < 2 by norm_num), Real.sin_sq_add_cos_sq (Real.pi / 18), Real.sin_sq_add_cos_sq (θ + Real.pi / 4), Real.sin_sq_add_cos_sq (θ), Real.sin_sq_add_cos_sq (Real.pi / 4), Real.sin_pos_of_pos_of_lt_pi (show 0 < Real.pi / 4 by linarith [Real.pi_pos] ) (show Real.pi / 4 < Real.pi by linarith [Real.pi_pos]), Real.sin_pos_of_pos_of_lt_pi (show 0 < Real.pi / 18 by linarith [Real.pi_pos] ) (show Real.pi / 18 < Real.pi by linarith [Real.pi_pos]), mul_pos (Real.sqrt_pos.mpr (show 0 < 2 by norm_num)) (Real.sqrt_pos.mpr (show 0 < 2 by norm_num)) ]
    have h5 : cos (θ + Real.pi / 4) = sin (Real.pi / 2 - (θ + Real.pi / 4)) := by
      rw [← Real.sin_pi_div_two_sub]
    rw [h5] at h2
    have h_eq2 : Real.pi / 18 = Real.pi / 2 - (θ + Real.pi / 4) := by
      apply Real.injOn_sin
      · -- Show that Real.pi / 18 is in [-(Real.pi / 2), Real.pi / 2]
        constructor
        · linarith [Real.pi_pos]
        · linarith [Real.pi_pos]
      · -- Show that Real.pi / 2 - (θ + Real.pi / 4) is in [-(Real.pi / 2), Real.pi / 2]
        constructor
        · -- Show that -(Real.pi / 2) ≤ Real.pi / 2 - (θ + Real.pi / 4)
          nlinarith [Real.pi_pos, hθ1, hθ2]
        · -- Show that Real.pi / 2 - (θ + Real.pi / 4) ≤ Real.pi / 2
          nlinarith [Real.pi_pos, hθ1, hθ2]
      exact h2
    have h_eq3 : θ = 35 * Real.pi / 180 := by
      linarith [Real.pi_pos, h_eq2]
      <;> ring_nf
      <;> nlinarith [Real.pi_pos]
    rw [h_eq3]
    field_simp [Real.pi_pos]
    <;> nlinarith [Real.pi_pos]
    <;> ring
  · -- Backward direction: if θ * 180 / π = 35 then sqrt 2 * sin (π / 18) = cos θ - sin θ
    intro h_eq
    have h_eq3 : θ = 35 * Real.pi / 180 := by
      field_simp [Real.pi_pos] at h_eq
      linarith
    rw [h_eq3]
    have h3 : cos (35 * Real.pi / 180) - sin (35 * Real.pi / 180) = sqrt 2 * sin (Real.pi / 18) := by
      have h4 : cos (35 * Real.pi / 180) - sin (35 * Real.pi / 180) = sqrt 2 * cos (35 * Real.pi / 180 + Real.pi / 4) := by
        rw [Real.cos_add, Real.cos_pi_div_four, Real.sin_pi_div_four]
        ring_nf
        <;> field_simp [Real.sqrt_pos.mpr, Real.sqrt_mul_self]
        <;> ring_nf
        <;> simp [mul_add, sub_eq_add_neg, mul_neg, neg_mul]
        <;> ring
      have h5 : cos (35 * Real.pi / 180 + Real.pi / 4) = sin (Real.pi / 18) := by
        have h6 : 35 * Real.pi / 180 + Real.pi / 4 = Real.pi / 2 - Real.pi / 18 := by
          linarith [Real.pi_pos]
          <;> ring_nf
          <;> nlinarith [Real.pi_pos]
        rw [h6]
        rw [Real.cos_pi_div_two_sub]
      rw [h4, h5]
      <;> nlinarith [Real.sqrt_pos.mpr (show 0 < 2 by norm_num), Real.sin_sq_add_cos_sq (Real.pi / 18), Real.sin_sq_add_cos_sq (35 * Real.pi / 180 + Real.pi / 4), Real.sin_sq_add_cos_sq (35 * Real.pi / 180), Real.sin_sq_add_cos_sq (Real.pi / 4), mul_pos (Real.sqrt_pos.mpr (show 0 < 2 by norm_num)) (Real.sqrt_pos.mpr (show 0 < 2 by norm_num)), Real.sin_pos_of_pos_of_lt_pi (show 0 < 35 * Real.pi / 180 by nlinarith [Real.pi_pos] ) (show 35 * Real.pi / 180 < Real.pi by nlinarith [Real.pi_pos] ) ]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sin_sq_add_cos_sq (Real.pi / 18), Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq (35 * Real.pi / 180), Real.sin_sq_add_cos_sq (Real.pi / 4), Real.sin_pos_of_pos_of_lt_pi (show 0 < Real.pi / 18 by linarith [Real.pi_pos] ) (show Real.pi / 18 < Real.pi by linarith [Real.pi_pos] ), Real.sin_pos_of_pos_of_lt_pi (show 0 < Real.pi / 4 by linarith [Real.pi_pos] ) (show Real.pi / 4 < Real.pi by linarith [Real.pi_pos] ), mul_pos (Real.sqrt_pos.mpr (show 0 < 2 by norm_num)) (Real.sqrt_pos.mpr (show 0 < 2 by norm_num) ) ]
    <;> ring_nf
    <;> nlinarith [Real.pi_pos]