import Mathlib

theorem algebra_19617 {A B C : ℝ} (hne : A ≠ 0) (ha : A = (1 + 40 / 100) * B) (hb : A = (1 - 30 / 100) * C) :
    B / C = 1 / 2 := by
  have eq1 : A = 1.4 * B := by
    rw [ha]
    ring_nf
  have eq2 : A = 0.7 * C := by
    rw [hb]
    ring_nf
  have eq3 : 1.4 * B = 0.7 * C := by
    linarith [eq1, eq2]
  have hc : C ≠ 0 := by
    by_contra h
    have hC : C = 0 := by linarith
    rw [hC] at hb
    have hA : A = 0 := by linarith
    contradiction
  have eq4 : B = (1 / 2) * C := by
    norm_num at eq3 ⊢
    linarith
  have h4 : B / C = 1 / 2 := by
    rw [eq4]
    have h_c_ne_zero : C ≠ 0 := hc
    field_simp [h_c_ne_zero]
    all_goals linarith
  exact h4