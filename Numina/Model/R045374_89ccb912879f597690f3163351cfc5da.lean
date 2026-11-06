import Mathlib

theorem inequalities_249945 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a < 1 ∧ b < 1 ∧ c < 1) :
    (1 - a) * (1 - b) * (1 - c) > 1 - (a + b + c) := by
  rcases h with ⟨ha1, hb1, hc1⟩
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < c := hc
  have h4 : 0 < 1 - a := by linarith
  have h5 : 0 < 1 - b := by linarith
  have h6 : 0 < 1 - c := by linarith
  have h7 : (1 - a) * (1 - b) * (1 - c) - (1 - (a + b + c)) > 0 := by
    nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - b by linarith), 
      mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - c by linarith), 
      mul_pos (show 0 < 1 - b by linarith) (show 0 < 1 - c by linarith), 
      mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - b by linarith), 
      mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - c by linarith), 
      mul_pos (show 0 < 1 - b by linarith) (show 0 < 1 - c by linarith), 
      mul_pos (mul_pos ha hb) (mul_pos ha hc), 
      mul_pos (mul_pos ha hb) (mul_pos hb hc), 
      mul_pos (mul_pos ha hc) (mul_pos hb hc)]
  linarith [h7]