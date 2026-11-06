import Mathlib

/- Andy, Beth, Charlie, and Daniel take a test with thirty questions. Andy and Beth together get the same number of questions wrong as Charlie and Daniel together. Andy and Daniel together get four more questions wrong than Beth and Charlie do together. If Charlie gets five questions wrong, how many questions does Andy get wrong? -/
theorem algebra_11174 (a b c d : ℕ)
    (h₀ : a + b = c + d) (h₁ : a + d = b + c + 4) (h₂ : c = 5) :
    a = 7 := by
  rw [h₂] at h₀ h₁
  omega