import Mathlib

theorem algebra_359
    {a b c : ℝ} (h₀ : a + b + c = 3) (h₁ : a^2 + b^2 + c^2 = 4) :
    (a^2 + b^2) / (2 - c) + (b^2 + c^2) / (2 - a) + (c^2 + a^2) / (2 - b) = 9 := by

  have h2 : c ≠ 2 := by
    by_contra h
    have hc : c = 2 := by linarith
    rw [hc] at h₀ h₁
    have h4 : a + b = 1 := by linarith
    have h5 : a^2 + b^2 = 0 := by nlinarith
    have ha1 : a^2 ≥ 0 := sq_nonneg a
    have hb1 : b^2 ≥ 0 := sq_nonneg b
    have ha2 : a^2 = 0 := by linarith [h5, ha1, hb1]
    have hb2 : b^2 = 0 := by linarith [h5, ha1, hb1]
    have ha : a = 0 := pow_eq_zero ha2
    have hb : b = 0 := pow_eq_zero hb2
    linarith

  have h3 : b ≠ 2 := by
    by_contra h
    have hb : b = 2 := by linarith
    rw [hb] at h₀ h₁
    have h4 : a + c = 1 := by linarith
    have h5 : a^2 + c^2 = 0 := by nlinarith
    have ha1 : a^2 ≥ 0 := sq_nonneg a
    have hc1 : c^2 ≥ 0 := sq_nonneg c
    have ha2 : a^2 = 0 := by linarith [h5, ha1, hc1]
    have hc2 : c^2 = 0 := by linarith [h5, ha1, hc1]
    have ha : a = 0 := pow_eq_zero ha2
    have hc : c = 0 := pow_eq_zero hc2
    linarith

  have h4 : a ≠ 2 := by
    by_contra h
    have ha : a = 2 := by linarith
    rw [ha] at h₀ h₁
    have h5 : b + c = 1 := by linarith
    have h6 : b^2 + c^2 = 0 := by nlinarith
    have hb1 : b^2 ≥ 0 := sq_nonneg b
    have hc1 : c^2 ≥ 0 := sq_nonneg c
    have hb2 : b^2 = 0 := by linarith [h6, hb1, hc1]
    have hc2 : c^2 = 0 := by linarith [h6, hb1, hc1]
    have hb : b = 0 := pow_eq_zero hb2
    have hc : c = 0 := pow_eq_zero hc2
    linarith

  have h5 : a^2 + b^2 = 4 - c^2 := by linarith

  have h6 : (a^2 + b^2) / (2 - c) = (2 + c) := by
    rw [h5]
    field_simp [(show 2 - c ≠ 0 by intro h; apply h2; linarith)]
    ring

  have h5' : b^2 + c^2 = 4 - a^2 := by linarith

  have h6' : (b^2 + c^2) / (2 - a) = (2 + a) := by
    rw [h5']
    field_simp [(show 2 - a ≠ 0 by intro h; apply h4; linarith)]
    ring

  have h5'' : c^2 + a^2 = 4 - b^2 := by linarith

  have h6'' : (c^2 + a^2) / (2 - b) = (2 + b) := by
    rw [h5'']
    field_simp [(show 2 - b ≠ 0 by intro h; apply h3; linarith)]
    ring

  calc
    (a^2 + b^2) / (2 - c) + (b^2 + c^2) / (2 - a) + (c^2 + a^2) / (2 - b)
        = (2 + c) + (2 + a) + (2 + b) := by rw [h6, h6', h6'']
    _ = 6 + (a + b + c) := by ring
    _ = 6 + 3 := by rw [h₀]
    _ = 9 := by norm_num