import Mathlib

/-In a sequence of positive integers each term after the first is $\frac{1}{3}$ of the sum of the term that precedes it and the term that follows it in the sequence. What is the 5th term of this sequence if the 1st term is 2 and the 4th term is 34?-/
theorem algebra_11007 {a : ℕ → ℤ} (ha : ∀ n, 0 < a n)
    (h : ∀ n, a (n + 1) = (a n + a (n + 2)) / (3 : ℝ))
    (ha1 : a 1 = 2) (ha4 : a 4 = 34) :
    a 5 = 89 := by
  clear ha
  -- first construct the equation when n = 2, 3, 4
  have ha₂ := h 1
  have ha₃ := h 2
  have ha₄ := h 3
  -- substitute the a 1 = 2, a 4 = 34
  norm_num at ha₂ ha₃ ha₄
  rw [ha1] at ha₂
  rw [ha4] at ha₃ ha₄
  -- first calculate a 3 = 13
  have ha3 : a 3 = 13 := by
    rw [ha₂] at ha₃
    field_simp at ha₃
    norm_num at ha₃
    replace ha₃ : ((a 3 * 9) : ℝ) = ((2 + a 3 + 102) : ℝ) := by convert ha₃
    norm_cast at ha₃
    linarith [ha₃]
  -- substitute a 3 = 34
  rw [ha3] at ha₄
  field_simp at ha₄
  ring_nf at ha₄
  norm_cast at ha₄
  linarith only [ha₄]
