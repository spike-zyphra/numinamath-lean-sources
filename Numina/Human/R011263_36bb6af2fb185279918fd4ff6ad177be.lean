import Mathlib

theorem algebra_1809 {a b c d : ℝ} (ha : a * b = 1) (hb : b + c = 0) (hc : b + c + d = 0)
(hd : b * c = -9) (he : c + a < d) : a + b = 10 / 3 := by
  have hc_eq : c = -b := by linarith
  rw [hc_eq] at hd
  have h1 : b ^ 2 = 9 := by
    have : b * (-b) = -9 := hd
    linarith
  have hb_eq : b = 3 ∨ b = -3 := by
    have h2 : b = 3 ∨ b = -3 := by
      have h1 : b ^ 2 = 9 := by linarith
      have : b = 3 ∨ b = -3 := sq_eq_sq_iff_eq_or_eq_neg.mp (by linarith)
      exact this
    exact h2
  cases hb_eq with
  | inl hb3 =>
    have hc3 : c = -3 := by
      rw [hb3] at hc_eq
      linarith
    have hd_eq : d = 0 := by
      have h3 : b + c + d = 0 := hc
      rw [hb3, hc3] at h3
      linarith
    have ha_eq : a = 1 / 3 := by
      rw [hb3] at ha
      have h4 : a * 3 = 1 := ha
      linarith
    rw [ha_eq, hb3]
    norm_num
  | inr hb3 =>
    have hc3 : c = 3 := by 
      rw [hb3] at hc_eq
      linarith
    have hd_eq : d = 0 := by 
      have h3 : b + c + d = 0 := hc
      rw [hb3, hc3] at h3
      linarith
    have ha_eq : a = -1 / 3 := by
      rw [hb3] at ha
      have h4 : a * (-3) = 1 := ha
      linarith
    have h5 : c + a < d := he
    rw [hc3, ha_eq, hd_eq] at h5
    norm_num at h5