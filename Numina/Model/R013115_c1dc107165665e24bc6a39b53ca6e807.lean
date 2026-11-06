import Mathlib

theorem number_theory_231427 (a b c : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (h : a * b * c < 10000) (h1 : 2 * a + 3 * b = c) (h2 : 4 * a + c + 1 = 4 * b) :
    a * b * c = 1118 := by
  have eq1 : b = 6 * a + 1 := by
    omega
  have eq2 : c = 20 * a + 3 := by
    have h1' : 2 * a + 3 * b = c := h1
    rw [eq1] at h1'
    omega
  have h3 : a ≤ 31 := by
    by_contra h4
    push_neg at h4
    have h4' : a ≥ 32 := by omega
    have h5 : c ≥ 643 := by
      omega
    have h6 : a * b * c ≥ 32 * 1 * 643 := by
      have h7 : a ≥ 32 := by omega
      have h8 : b ≥ 1 := by
        have h8 : b ≥ 1 := by nlinarith
        omega
      have h9 : c ≥ 643 := by
        omega
      have h10 : a * b ≥ 32 * 1 := by
        have ha1 : a ≥ 32 := by omega
        have hb1 : b ≥ 1 := by nlinarith
        nlinarith
      nlinarith
    have h7 : a * b * c < 10000 := h
    nlinarith
  interval_cases a <;> norm_num [eq1, eq2] at ha hb hc h ⊢
  <;> all_goals
    try { tauto }