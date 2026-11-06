import Mathlib

theorem number_theory_3265
    (a : ℤ)
    (h : a^3 = 10503459) :
    a = 219 := by
  have h1: a^3 - 10503459 = 0 := by
    rw [h]
    simp
  have h2: a = 219 := by
    have ht1: a^3 - 10503459 = (a - 219) * (a^2 + 219*a + 219^2) := by ring
    rw [ht1] at h1
    cases' (mul_eq_zero.mp h1) with h2 h3
    · -- a - 219 = 0
      linarith
    · -- a^2 + 219a + 219^2 = 0
      have ht2: a = 0 ∨ a = -219 := by nlinarith
      rcases ht2 with h4 | h5
      · rw [h4] at h
        norm_num at h
      · rw [h5] at h
        norm_num at h
  exact h2