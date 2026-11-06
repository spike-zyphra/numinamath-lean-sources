import Mathlib

theorem inequalities_598175 (a b c : ℝ) (ha : a ∈ Set.Ioo (-1) 1) (hb : b ∈ Set.Ioo (-1) 1) (hc : c ∈ Set.Ioo (-1) 1) :
    a * b * c + 2 > a + b + c := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  have h1 : 0 < 1 - a := by linarith 
  have h2 : 0 < 1 + a := by linarith 
  have h3 : 0 < 1 - b := by linarith 
  have h4 : 0 < 1 + b := by linarith 
  have h5 : 0 < 1 - c := by linarith 
  have h6 : 0 < 1 + c := by linarith 
  nlinarith [mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - b by linarith), 
          mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 - c by linarith), 
          mul_pos (show 0 < 1 - b by linarith) (show 0 < 1 - c by linarith), 
          mul_pos (show 0 < 1 + a by linarith) (show 0 < 1 + b by linarith), 
          mul_pos (show 0 < 1 + a by linarith) (show 0 < 1 + c by linarith), 
          mul_pos (show 0 < 1 + b by linarith) (show 0 < 1 + c by linarith), 
          mul_pos (show 0 < 1 - a by linarith) (show 0 < 1 + a by linarith), 
          mul_pos (show 0 < 1 - b by linarith) (show 0 < 1 + b by linarith), 
          mul_pos (show 0 < 1 - c by linarith) (show 0 < 1 + c by linarith)]