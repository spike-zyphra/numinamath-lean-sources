import Mathlib

theorem algebra_215292 (a b c d : ℕ) (ha : a ≠ b) (hb : a ≠ c) (hc : a ≠ d)
    (hd : b ≠ c) (he : b ≠ d) (hf : c ≠ d) (h1 : 1 ≤ a ∧ a ≤ 20) (h2 : 1 ≤ b ∧ b ≤ 20)
    (h3 : 1 ≤ c ∧ c ≤ 20) (h4 : 1 ≤ d ∧ d ≤ 20) :
    (2 * a + b : ℚ) / (c * 2 + d) ≥ 4 / 59 := by
  rcases h1 with ⟨ha1, ha2⟩
  rcases h2 with ⟨hb1, hb2⟩
  rcases h3 with ⟨hc1, hc2⟩
  rcases h4 with ⟨hd1, hd2⟩
  by_contra h
  push_neg at h
  have h5 : (2 * a + b : ℚ) / (c * 2 + d) < (4 / 59 : ℚ) := by linarith
  have h6 : (2 * a + b : ℚ) * (59 : ℚ) < (4 : ℚ) * ((c * 2 + d) : ℚ) := by 
    have h_pos1 : (c * 2 + d : ℚ) > 0 := by
      have hc1' : (c : ℚ) ≥ (1 : ℚ) := by exact_mod_cast hc1
      have hd1' : (d : ℚ) ≥ (1 : ℚ) := by exact_mod_cast hd1
      nlinarith
    have h_pos2 : (59 : ℚ) > 0 := by norm_num
    apply (div_lt_div_iff (by positivity) (by positivity)).mp at h5
    linarith
  have h7 : (2 * a + b) * 59 < 4 * (c * 2 + d) := by 
    exact_mod_cast h6
  have h7' : a ≤ 20 := by linarith
  have h8' : b ≤ 20 := by linarith
  have h9' : c ≤ 20 := by linarith
  have h10' : d ≤ 20 := by linarith
  interval_cases a <;> interval_cases b
  <;> omega