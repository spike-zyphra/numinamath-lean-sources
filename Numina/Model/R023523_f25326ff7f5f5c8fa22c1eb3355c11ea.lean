import Mathlib

theorem algebra_179252 {f : ℝ → ℝ} (hf : ∃ a b c, f = fun x => a*x^2 + b*x + c)
    (h0 : f 0 = Real.sin 0) (hπ2 : f (Real.pi / 2) = Real.sin (Real.pi / 2)) (hπ : f Real.pi = Real.sin Real.pi) :
    f = fun x => -4 / Real.pi^2 * x^2 + 4 / Real.pi * x := by 
  rcases hf with ⟨a, b, c, rfl⟩
  have h1 : a * 0 ^ 2 + b * 0 + c = Real.sin 0 := by simpa using h0
  have h2 : a * (Real.pi / 2) ^ 2 + b * (Real.pi / 2) + c = Real.sin (Real.pi / 2) := by simpa using hπ2
  have h3 : a * Real.pi ^ 2 + b * Real.pi + c = Real.sin Real.pi := by simpa using hπ
  have hc : c = 0 := by
    simp [Real.sin_zero] at h1
    linarith
  have h2' : a * (Real.pi / 2) ^ 2 + b * (Real.pi / 2) + c = 1 := by
    have h4 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    rw [h4] at h2
    linarith
  have h3' : a * Real.pi ^ 2 + b * Real.pi + c = 0 := by
    have h4 : Real.sin Real.pi = 0 := by
      rw [Real.sin_pi]
      all_goals linarith
    rw [h4] at h3
    linarith
  rw [hc] at h2' h3'
  have h4 : b = -a * Real.pi := by
    have h5 : Real.pi * (a * Real.pi + b) = 0 := by
      nlinarith [Real.pi_pos]
    have h5 : a * Real.pi + b = 0 := by
      apply (mul_left_inj' (show Real.pi ≠ 0 by
        exact Real.pi_ne_zero)).mp
      linarith
    nlinarith [Real.pi_pos]
  have ha : a = -4 / Real.pi ^ 2 := by
    rw [show b = -a * Real.pi by linarith [h4]] at h2'
    field_simp [show Real.pi ≠ 0 by exact Real.pi_ne_zero] at h2' ⊢
    <;> nlinarith [Real.pi_pos]
  have hb : b = 4 / Real.pi := by
    rw [ha] at h4
    have h5 : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp [h5] at h4 ⊢
    <;> nlinarith [Real.pi_pos]
  funext x
  simp [ha, hb, hc]
  all_goals field_simp [show Real.pi ≠ 0 by exact Real.pi_ne_zero]
  all_goals ring_nf <;> field_simp [show Real.pi ≠ 0 by exact Real.pi_ne_zero] <;> ring