import Mathlib

theorem inequalities_65388 (a b c : ℝ) (ha : a + b + c > 0) (hb : b * c + c * a + a * b > 0)
    (hc : a * b * c > 0) : a > 0 ∧ b > 0 ∧ c > 0 := by
  have ha1 : a > 0 := by
    by_contra h1
    push_neg at h1
    have h2 : b * c < 0 := by
      nlinarith [h1, hc]
    nlinarith [h1, ha, hb, h2]
  have hb1 : b > 0 := by
    by_contra h1
    push_neg at h1
    have h2 : a * c < 0 := by
      nlinarith [h1, hc]
    nlinarith [h1, ha, hb, h2]
  have hc1 : c > 0 := by
    by_contra h1
    push_neg at h1
    have h2 : a * b < 0 := by
      nlinarith [h1, hc]
    nlinarith [h1, ha, hb, h2]
  exact ⟨ha1, hb1, hc1⟩