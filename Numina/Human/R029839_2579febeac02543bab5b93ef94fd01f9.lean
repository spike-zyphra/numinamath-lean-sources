import Mathlib
open Real

/-
Compute $\frac{\tan ^{2}\left(20^{\circ}\right)-\sin ^{2}\left(20^{\circ}\right)}{\tan ^{2}\left(20^{\circ}\right) \sin ^{2}\left(20^{\circ}\right)}$.
-/
theorem algebra_611085 : ((tan (π / 9))^2 - (sin (π / 9))^2)/ ((tan (π / 9))^2 * (sin (π / 9))^2)  = 1 := by

  let x:ℝ:= π / 9;
  have hx: x =  π / 9 := rfl;
  rw [←hx]
  rw [tan_eq_sin_div_cos]
  field_simp

  -- Show that cos x ≠ 0
  have hcos: cos x > 0 := by
    unfold x
    apply cos_pos_of_le_one
    have _1: π / 9 ≥ 0 := by linarith[pi_pos]

    have abs: |π / 9| = π / 9 := by
      apply abs_of_nonneg
      linarith
    rw [abs]
    linarith [pi_le_four]

  -- Show that sin x ≠ 0
  have hsin: sin x > 0 := by
    unfold x
    apply sin_pos_of_pos_of_le_one
    norm_num
    exact by linarith [pi_pos]
    have _9 : 9>0 := by norm_num
    have h18: π ≤ 9 := by linarith [pi_le_four]
    linarith

  -- Remove fraction
  field_simp [hcos]
  have cos_sq_1: 1 - cos x ^ 2 = sin x ^ 2 := by rw [sin_sq x]

  -- Calculate the result
  calc
    _ = (sin x ^ 2)*(1 - cos x ^ 2) := by ring_nf
    _ = _ := by rw[cos_sq_1]