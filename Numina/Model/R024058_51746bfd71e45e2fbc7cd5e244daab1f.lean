import Mathlib

theorem inequalities_191590 (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : (a / 11 : ℝ) < (7 / b : ℝ) ∧ (7 / b : ℝ) < (4 / 5 : ℝ)) :
    a + b ≤ 77 := by
  have h1 : (a / 11 : ℝ) < (7 / b : ℝ) := h.1
  have h2 : (7 / b : ℝ) < (4 / 5 : ℝ) := h.2
  have h3 : (a : ℝ) * (b : ℝ) < (77 : ℝ) := by
    have h1' : (a / 11 : ℝ) < (7 / (b : ℝ)) := h1
    have pos1 : (11 : ℝ) > (0 : ℝ) := by norm_num
    have pos2 : (b : ℝ) > (0 : ℝ) := by
      exact_mod_cast show (b : ℝ) > (0 : ℝ) from by
        have hb' : b > 0 := by
          by_contra h
          push_neg at h
          have : b = 0 := by linarith
          contradiction
        exact_mod_cast hb'
    have h4 : (a : ℝ) * (b : ℝ) < (77 : ℝ) := by
      apply (div_lt_div_iff (by linarith) (by linarith)).mp at h1'
      nlinarith
    linarith
  have h5 : (7 : ℝ) * (5 : ℝ) < (4 : ℝ) * (b : ℝ) := by
    have h2' : (7 / b : ℝ) < (4 / 5 : ℝ) := h2
    have pos1 : (b : ℝ) > (0 : ℝ) := by
      exact_mod_cast show (b : ℝ) > (0 : ℝ) from by
        have hb' : b > 0 := by
          by_contra h
          push_neg at h
          have : b = 0 := by linarith
          contradiction
        exact_mod_cast hb'
    have pos2 : (5 : ℝ) > (0 : ℝ) := by norm_num
    apply (div_lt_div_iff (by linarith) (by linarith)).mp at h2'
    nlinarith
  have h6 : a * b < 77 := by
    have h3' : (a * b : ℝ) < (77 : ℝ) := h3
    have h7 : (a * b : ℝ) = (a * b : ℕ) := by
      simp
    rw [h7] at h3'
    have h8 : (a * b : ℕ) < 77 := by
      by_contra h
      push_neg at h
      have h9 : (a * b : ℕ) ≥ 77 := by 
        omega
      have h10 : (a * b : ℝ) ≥ (77 : ℝ) := by
        exact_mod_cast h9
      linarith
    omega
  have h8 : 35 < 4 * (b : ℕ) := by
    have h9 : (7 : ℝ) * (5 : ℝ) < (4 : ℝ) * (b : ℝ) := h5
    have h11 : (4 * (b : ℕ) : ℝ) = (4 * (b : ℝ) : ℝ) := by 
      simp
    have h12 : (35 : ℝ) = (35 : ℝ) := by 
      simp
    have h13 : (35 : ℝ) < (4 * (b : ℝ) : ℝ) := by
      nlinarith
    have h14 : (35 : ℕ) < (4 * (b : ℕ) : ℕ) := by
      by_contra h
      push_neg at h
      have h15 : (4 * (b : ℕ) : ℕ) ≤ 35 := by
        omega
      have h16 : (4 * (b : ℕ) : ℝ) ≤ (35 : ℝ) := by
        exact_mod_cast h15
      nlinarith
    omega
  by_contra h
  push_neg at h
  have h15 : a + b > 77 := by
    omega
  have h16 : a > 0 := by
    by_contra h
    push_neg at h
    have : a = 0 := by
      linarith
    contradiction
  have h17 : b > 0 := by
    by_contra h
    push_neg at h
    have : b = 0 := by
      linarith
    contradiction
  have h18 : b ≥ 9 := by 
    omega
  have h19 : a ≤ 8 := by
    nlinarith [h6, h18]
  nlinarith [h6, h8, h15, h19]