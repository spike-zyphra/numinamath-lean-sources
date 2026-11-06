import Mathlib

theorem algebra_227247 (v_h v_a d : ℝ) (h_v : v_h > 0) (h_a : v_a > 0)
    (h_meeting : d / v_h = d / v_a - 100 / v_a) (h_h : d / v_h = 3 * v_a) (h_a' : d / v_a = 1 * v_h + 20 / 60) :
    v_h = 500 ∧ v_a = 300 ∧ d = 500 := by 
  have eq1 : d * v_a = d * v_h - 100 * v_h := by
    have h1 : v_h ≠ 0 := by linarith
    have h2 : v_a ≠ 0 := by linarith
    field_simp [h1, h2] at h_meeting ⊢
    nlinarith
  have eq2 : d = 3 * v_a * v_h := by
    have h1 : v_h ≠ 0 := by linarith
    field_simp [h1] at h_h ⊢
    nlinarith
  have eq3 : 3 * v_a * v_h = (v_h + (20 / 60)) * v_a := by
    have h1 : v_a ≠ 0 := by linarith
    field_simp [h1] at h_a' ⊢
    nlinarith
  -- Solve for `v_h` from `eq3` using `h_a`
  have h3 : 3 * v_h = v_h + (20 / 60) := by
    apply (mul_left_inj' (show v_a ≠ 0 by linarith)).mp
    linarith [eq3]
  have h4 : 2 * v_h = 1 / 3 := by
    nlinarith [h3]
  have h5 : v_h = 1 / 6 := by
    nlinarith [h4]
  rw [show v_h = 1 / 6 by linarith [h5]] at eq2
  have h6 : d = (1 / 2) * v_a := by
    nlinarith [eq2]
  rw [show d = (1 / 2) * v_a by linarith [h6]] at eq1
  -- Substituting `d = (1/2) * v_a` and `v_h = 1/6` into `eq1`
  -- We get a quadratic equation for `v_a` which gives complex solutions
  -- Since we assumed `v_a > 0` we reach a contradiction
  nlinarith [sq_pos_of_pos h_a, sq_nonneg (v_a - 300 / (1 : ℝ)), sq_nonneg (d - 500 / (1 : ℝ)), h5, h6, h_a, h_v]