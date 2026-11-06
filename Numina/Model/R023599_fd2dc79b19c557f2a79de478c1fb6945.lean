import Mathlib

theorem number_theory_291013 (a b c : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c) (h : a + b * c = 37) :
    a + b - c ≤ 32 := by
  have h1 : a ≤ 37 := by
    have : b * c ≥ 0 := by positivity
    linarith
  have h2 : b ≤ 37 := by
    by_contra h2
    push_neg at h2
    have h3 : b * c ≥ 38 := by
      have : c ≥ 1 := by
        by_contra h
        push_neg at h
        interval_cases c <;> tauto
      nlinarith
    omega
  have h3 : c ≤ 37 := by
    by_contra h3
    push_neg at h3
    have h4 : b * c ≥ 38 := by
      have : b ≥ 1 := by
        by_contra h
        push_neg at h
        interval_cases b <;> tauto
      nlinarith
    omega
  interval_cases b <;> interval_cases c <;> norm_num at h hdist ha hb hc <;> omega