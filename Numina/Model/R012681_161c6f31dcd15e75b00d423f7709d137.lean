import Mathlib

theorem algebra_227599 {a b c : ℝ} (h : (a^2 - b * c) / (a * (1 - b * c)) = (b^2 - a * c) / (b * (1 - a * c))) (h' : a * b * c * (1 - b * c) * (1 - a * c) ≠ 0) (h'' : a ≠ b) :
    a + b + c = 1 / a + 1 / b + 1 / c := by
  have ha : a ≠ 0 := by
    intro ha
    have : a * b * c * (1 - b * c) * (1 - a * c) = 0 := by
      rw [ha]
      norm_num
    contradiction

  have hb : b ≠ 0 := by
    intro hb
    have : a * b * c * (1 - b * c) * (1 - a * c) = 0 := by
      rw [hb]
      norm_num
    contradiction

  have hc : c ≠ 0 := by
    intro hc
    have : a * b * c * (1 - b * c) * (1 - a * c) = 0 := by
      rw [hc]
      norm_num
    contradiction

  have h1 : 1 - b * c ≠ 0 := by
    intro h1
    have : a * b * c * (1 - b * c) * (1 - a * c) = 0 := by
      rw [show 1 - b * c = 0 by linarith]
      norm_num
    contradiction

  have h2 : 1 - a * c ≠ 0 := by
    intro h2
    have : a * b * c * (1 - b * c) * (1 - a * c) = 0 := by
      rw [show 1 - a * c = 0 by linarith]
      norm_num
    contradiction

  have eq1 : b * (1 - a * c) * (a^2 - b * c) = a * (1 - b * c) * (b^2 - a * c) := by
    have h1 : a * (1 - b * c) ≠ 0 := by
      apply mul_ne_zero
      exact ha
      exact h1
    have h2 : b * (1 - a * c) ≠ 0 := by
      apply mul_ne_zero
      exact hb
      exact h2
    field_simp [h1, h2] at h ⊢
    linarith

  have eq4 : a * b * c * (a + b + c) = a * b + a * c + b * c := by
    apply (mul_left_inj' (show a - b ≠ 0 by intro h0; apply h''; linarith)).mp
    nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_pos_of_ne_zero h1, sq_pos_of_ne_zero h2]

  have eq7 : (b * c + a * c + a * b) / (a * b * c) = 1 / a + 1 / b + 1 / c := by
    have h8 : a * b * c ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      exact ha
      exact hb
      exact hc
    field_simp [h8, ha, hb, hc]
    <;> nlinarith

  have eq6 : a + b + c = (b * c + a * c + a * b) / (a * b * c) := by
    have h8 : a * b * c ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      exact ha
      exact hb
      exact hc
    field_simp [h8] at *
    nlinarith [eq4, sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc, sq_pos_of_ne_zero h1, sq_pos_of_ne_zero h2]

  linarith [eq6, eq7]