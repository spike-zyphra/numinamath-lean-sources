import Mathlib

theorem number_theory_14360 (p q : ℤ) (hp : 0 < p) (hq : 0 < q) (h : 5 / 9 < (p / q : ℝ) ∧ (p / q : ℝ) < 4 / 7)
(hq1 : ∀ p' q' : ℤ, 0 < p' → 0 < q' → (5 / 9 < (p' / q' : ℝ) ∧ (p' / q' : ℝ) < 4 / 7) → q ≤ q') : q - p = 7 := by
  have h1 : (5 : ℝ) / 9 < (p / q : ℝ) := h.1
  have h2 : (p / q : ℝ) < (4 / 7 : ℝ) := h.2
  have h3 : 5 * q < 9 * p := by
    have h1' : (5 : ℝ) / 9 < (p / q : ℝ) := h1
    have h3 : (5 * q : ℝ) < 9 * p := by
      have h3 : (p : ℝ) / (q : ℝ) > (5 / 9 : ℝ) := by linarith
      have h4 : (p : ℝ) / (q : ℝ) > (5 / 9 : ℝ) := h3
      have h5 : (5 * (q : ℝ) : ℝ) < 9 * (p : ℝ) := by
        have h5 : (q : ℝ) > 0 := by exact_mod_cast hq
        have h6 : (p : ℝ) / (q : ℝ) > (5 / 9 : ℝ) := h4
        have h7 : (5 * (q : ℝ) : ℝ) < 9 * (p : ℝ) := by
          have h8 : (q : ℝ) > 0 := h5
          apply (div_lt_div_iff (by positivity) (by positivity)).mp at h6
          linarith
        linarith
      linarith
    exact_mod_cast h3
  have h4 : 7 * p < 4 * q := by
    have h2' : (p / q : ℝ) < (4 / 7 : ℝ) := h2
    have h4 : (7 * p : ℝ) < 4 * q := by
      have h3 : (p : ℝ) / (q : ℝ) < (4 / 7 : ℝ) := by linarith
      have h4 : (p : ℝ) / (q : ℝ) < (4 / 7 : ℝ) := h3
      have h5 : (7 * (p : ℝ) : ℝ) < 4 * (q : ℝ) := by
        have h5 : (q : ℝ) > 0 := by exact_mod_cast hq
        have h6 : (p : ℝ) / (q : ℝ) < (4 / 7 : ℝ) := h4
        have h7 : (7 * (p : ℝ) : ℝ) < 4 * (q : ℝ) := by
          have h8 : (q : ℝ) > 0 := h5
          apply (div_lt_div_iff (by positivity) (by positivity)).mp at h6
          linarith
        linarith
      linarith
    exact_mod_cast h4
  have h5 := hq1 9 16 (by norm_num) (by norm_num) (by norm_num)
  have h6 : q ≥ 16 := by
    by_contra h7
    push_neg at h7
    have h7 : q ≤ 15 := by omega
    interval_cases q <;> omega
  have h7 : q = 16 := by
    linarith
  have h8 : p = 9 := by
    linarith
  rw [h7, h8]
  all_goals norm_num