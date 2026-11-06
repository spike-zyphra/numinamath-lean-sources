import Mathlib

/-In an arithmetic sequence, the 7th term is 30, and the 11th term is 60. What is the 21st term of this sequence?-/
theorem algebra_21436 (a d : ℝ) (h₀ : a + 6 * d = 30) (h₁ : a + 10 * d = 60) :
    a + 20 * d = 135 := by
  -- show that d = 15 / 2
  have hd : d = 15 / 2 := by linarith only [h₀, h₁]
  -- calculate the conclusion
  calc
    a + 20 * d = (a + 10 * d) + 10 * d := by ring_nf
    _ = 60 + 10 * (15 / 2) := by rw [h₁, hd]
    _ = 135 := by norm_num