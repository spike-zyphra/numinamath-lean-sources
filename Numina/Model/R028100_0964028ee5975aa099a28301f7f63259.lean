import Mathlib

theorem number_theory_13788 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : 90 < a + b ∧ a + b < 99) (h' : 0.9 < (a / b : ℝ) ∧ (a / b : ℝ) < 0.91) :
    a * b = 2346 := by
  rcases h with ⟨h1, h2⟩
  rcases h' with ⟨h3, h4⟩
  have h5 : (a : ℝ) > (0 : ℝ) := by
    exact_mod_cast (show 0 < a by linarith)
  have h6 : (b : ℝ) > (0 : ℝ) := by
    exact_mod_cast (show 0 < b by linarith)
  have h7 : (9 : ℝ) * (b : ℝ) < (10 : ℝ) * (a : ℝ) := by
    have h8 : (a / b : ℝ) > (0.9 : ℝ) := by linarith
    have h9 : (a / b : ℝ) > (9 / 10 : ℝ) := by
      norm_num at h8 ⊢
      linarith
    have h10 : (10 : ℝ) * (a : ℝ) > (9 : ℝ) * (b : ℝ) := by
      have h11 : (a : ℝ) / (b : ℝ) > (9 / 10 : ℝ) := h9
      apply (lt_div_iff₀ h6).mp at h11
      linarith
    linarith
  have h8 : 10 * a > 9 * b := by
    have h9 : (10 : ℝ) * (a : ℝ) > (9 : ℝ) * (b : ℝ) := h7
    exact_mod_cast (show (10 * a : ℝ) > (9 * b : ℝ) by linarith [h9])
  have h13 : (100 : ℝ) * (a : ℝ) < (91 : ℝ) * (b : ℝ) := by
    have h11 : (a / b : ℝ) < (0.91 : ℝ) := by linarith
    have h12 : (a / b : ℝ) < (91 / 100 : ℝ) := by
      norm_num at h11 ⊢
      linarith
    have h13 : (100 : ℝ) * (a : ℝ) < (91 : ℝ) * (b : ℝ) := by
      have h14 : (a : ℝ) / (b : ℝ) < (91 / 100 : ℝ) := h12
      apply (div_lt_iff₀ h6).mp at h14
      linarith
    linarith
  have h9 : 100 * a < 91 * b := by
    have h10 : (100 : ℝ) * (a : ℝ) < (91 : ℝ) * (b : ℝ) := h13
    exact_mod_cast (show (100 * a : ℝ) < (91 * b : ℝ) by linarith [h10])
  have h10 : a ≤ 97 := by
    omega
  have h11 : b ≤ 97 := by
    omega
  interval_cases a <;> omega
  <;> norm_num at h1 h2 h3 h4 h8 h9
  <;> all_goals
    { 
      have h21 : a ≤ 98 := by
        omega
      have h22 : b ≤ 98 := by
        omega
      interval_cases a <;> omega
    }
  all_goals
    linarith
  all_goals
    linarith
  all_goals
    try { nlinarith }