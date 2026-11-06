import Mathlib

theorem algebra_12186 {a b c d e f : ℝ} (hb : b = 1) (he : e = -a - c) (hsum : a + b * Complex.I + (c + d * Complex.I) + (e + f * Complex.I) = - Complex.I) :
    d + f = -2 := by
  simp [Complex.ext_iff] at hsum 
  rcases hsum with ⟨hreal, himag⟩
  rw [hb] at himag 
  linarith