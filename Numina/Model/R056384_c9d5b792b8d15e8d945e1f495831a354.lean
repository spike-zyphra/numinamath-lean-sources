import Mathlib

theorem algebra_189216 {x : ℝ} (hx : x^3 + 4 * x = 8) :
    x^7 + 64 * x^2 = 128 := by
  have h1 : x^3 = 8 - 4 * x := by linarith
  have h2 : x^4 = 8 * x - 4 * x^2 := by 
    calc
      x^4 = x * x^3 := by ring
      _   = x * (8 - 4 * x) := by rw [h1]
      _   = 8 * x - 4 * x^2 := by ring
  have h3 : x^5 = 8 * x^2 + 16 * x - 32 := by 
    calc 
      x^5 = x * x^4 := by ring
      _   = x * (8 * x - 4 * x^2) := by rw [h2]
      _   = 8 * x^2 - 4 * x^3 := by ring
      _   = 8 * x^2 - 4 * (8 - 4 * x) := by rw [h1]
      _   = 8 * x^2 - 32 + 16 * x := by ring
      _   = 8 * x^2 + 16 * x - 32 := by ring
  have h4 : x^6 = 16 * x^2 - 64 * x + 64 := by 
    calc 
      x^6 = x * x^5 := by ring
      _   = x * (8 * x^2 + 16 * x - 32) := by rw [h3]
      _   = 8 * x^3 + 16 * x^2 - 32 * x := by ring
      _   = 8 * (8 - 4 * x) + 16 * x^2 - 32 * x := by rw [h1]
      _   = 64 - 32 * x + 16 * x^2 - 32 * x := by ring
      _   = 16 * x^2 - 64 * x + 64 := by ring
  have h5 : x^7 = 128 - 64 * x^2 := by 
    calc 
      x^7 = x * x^6 := by ring
      _   = x * (16 * x^2 - 64 * x + 64) := by rw [h4]
      _   = 16 * x^3 - 64 * x^2 + 64 * x := by ring
      _   = 16 * (8 - 4 * x) - 64 * x^2 + 64 * x := by rw [h1]
      _   = 128 - 64 * x - 64 * x^2 + 64 * x := by ring
      _   = 128 - 64 * x^2 := by ring
  linarith [h5]