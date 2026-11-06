import Mathlib

theorem algebra_220626 {a b c : ℝ} (h₀ : a + b + c = 0) (h₁ : a^3 + b^3 + c^3 = 0) :
    a^2009 + b^2009 + c^2009 = a^2011 + b^2011 + c^2011 := by
  have h2 : c = -a - b := by linarith
  rw [h2] at h₁
  have h3 : 3 * a * b * (a + b) = 0 := by
    ring_nf at h₁ ⊢
    linarith

  cases' (mul_eq_zero.mp h3) with h4 h5
  cases' (mul_eq_zero.mp h4) with h6 h7
  · -- Case $a = 0$
    have ha0 : a = 0 := by linarith
    have hc0 : c = -b := by
      rw [ha0] at h2
      linarith
    rw [ha0, hc0]
    all_goals ring_nf
  · -- Case $b = 0$
    have hb0 : b = 0 := by linarith
    have hc0 : c = -a := by
      rw [hb0] at h2
      linarith
    rw [hb0, hc0]
    all_goals ring_nf
  · -- Case $a + b = 0$
    have h5' : a + b = 0 := by linarith
    have hc0 : c = 0 := by
      nlinarith
    rw [hc0]
    have hb2 : b = -a := by linarith
    rw [hb2]
    all_goals ring_nf
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith