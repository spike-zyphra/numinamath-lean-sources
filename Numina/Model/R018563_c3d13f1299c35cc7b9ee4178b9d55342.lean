import Mathlib

theorem algebra_96917 (d v : ℝ) (h : v > 0) (h1 : d / (v + 0.5) = 4 / 5 * d / v) (h2 : d / (v - 0.5) = d / v + 2.5) :
    d = 15 := by

  have h1' : d ≠ 0 := by
    by_contra hd
    rw [hd] at h1 h2
    norm_num at h1 h2
  have h11 : v ≠ 0 := by
    nlinarith
  have h3 : v = 2 := by
    have h111 : v + 0.5 ≠ 0 := by
      linarith
    have eq1 : d * v = 4 / 5 * (d * (v + 0.5)) := by
      field_simp [h111, h11] at h1
      ring_nf at h1 ⊢
      nlinarith
    -- simplify by cancelling d
    apply (mul_left_inj' h1').mp
    ring_nf at eq1 ⊢
    nlinarith
  have h4 : d = 15 := by
    rw [h3] at h2
    field_simp [(show (2 : ℝ) - 0.5 ≠ 0 by norm_num), (show (2 : ℝ) ≠ 0 by norm_num)] at h2 
    norm_num at h2 ⊢
    nlinarith
  exact_mod_cast h4