import Mathlib

open Real Set
open scoped Real

theorem calculus_12453 {n : ℤ} (hn : n ∈ Ioo (-90) 90) :
    tan (n * π / 180) = tan (312 * π / 180) ↔ n = -48 := by
  rw [mem_Ioo] at hn
  constructor
  · -- Forward direction: if $\tan(n°) = \tan(312°)$ and $-90 < n < 90$, then $n = -48$
    intro h
    have h1 : -90 < n := hn.1
    have h2 : n < 90 := hn.2
    have htan : tan (n * π / 180) = tan (312 * π / 180) := h
    have h5 : n * π / 180 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · -- Show left endpoint
        have hn1 : (n : ℝ) > (-90 : ℝ) := by
          exact_mod_cast h1
        have h6 : n * π / 180 > - (Real.pi / 2) := by
          nlinarith [Real.pi_pos, Real.pi_gt_three]
        linarith
      · -- Show right endpoint
        have hn2 : (n : ℝ) < (90 : ℝ) := by
          exact_mod_cast h2
        have h7 : n * π / 180 < Real.pi / 2 := by
          nlinarith [Real.pi_pos, Real.pi_gt_three]
        linarith
    have h6 : 312 * π / 180 = -48 * π / 180 + 2 * Real.pi := by
      linarith [Real.pi_pos]
    have htan_eq : tan (312 * π / 180) = tan (-48 * π / 180) := by
      rw [show 312 * π / 180 = -48 * π / 180 + 2 * Real.pi by linarith [Real.pi_pos]]
      have htan_periodic : tan (-48 * π / 180 + 2 * Real.pi) = tan (-48 * π / 180) := by
        rw [show -48 * π / 180 + 2 * Real.pi = (-48 * π / 180) + Real.pi + Real.pi by ring]
        rw [tan_add_pi, tan_add_pi]
      rw [htan_periodic]
    rw [htan_eq] at htan
    have h7 : -48 * π / 180 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor
      · -- Show left endpoint
        have h8 : -48 * Real.pi / 180 > - (Real.pi / 2) := by
          nlinarith [Real.pi_pos, Real.pi_gt_three]
        linarith
      · -- Show right endpoint
        have h9 : -48 * Real.pi / 180 < Real.pi / 2 := by
          nlinarith [Real.pi_pos, Real.pi_gt_three]
        linarith
    have h8 : n * π / 180 = -48 * π / 180 := by
      apply Real.injOn_tan h5 h7 htan
    have h9 : (n : ℝ) * π / 180 = (-48 : ℝ) * π / 180 := by
      linarith [h8]
    have h10 : (n : ℝ) = (-48 : ℝ) := by
      have h_ne : Real.pi / 180 ≠ 0 := by
        nlinarith [Real.pi_pos]
      have h11 : (n : ℝ) * (Real.pi / 180) = (-48 : ℝ) * (Real.pi / 180) := by
        linarith [h9]
      have h12 : (n : ℝ) = (-48 : ℝ) := by
        apply (mul_left_inj' h_ne).mp
        linarith
      exact h12
    exact_mod_cast h10
  · -- Backward direction: if n = -48, then $\tan(n°) = \tan(312°)$
    intro h
    rw [h]
    have h4 : 312 * π / 180 = -48 * π / 180 + 2 * Real.pi := by
      linarith [Real.pi_pos]
    rw [h4]
    have htan_periodic : tan (-48 * π / 180 + 2 * Real.pi) = tan (-48 * π / 180) := by
      rw [show -48 * π / 180 + 2 * Real.pi = (-48 * π / 180) + Real.pi + Real.pi by ring]
      rw [tan_add_pi, tan_add_pi]
    rw [htan_periodic]
    all_goals linarith [Real.pi_pos]