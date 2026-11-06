import Mathlib

theorem algebra_1592 {a b : ℝ} (ha : a < 0) (hab : a * b < 0) : abs (b - a + 1) - abs (a - b - 5) = -4 := by
  have hb1 : b > 0 := by 
    have h1 : a < 0 := ha
    have h2 : a * b < 0 := hab
    apply mul_neg_iff.mp at h2
    cases h2 with
    | inl h =>
      linarith
    | inr h =>
      linarith
  
  have h1 : abs (b - a + 1) = b - a + 1 := by
    have h2 : b - a + 1 > 0 := by
      have hb' : b > 0 := hb1
      have ha' : a < 0 := ha
      linarith
    rw [abs_of_pos h2]

  have h2 : abs (a - b - 5) = -(a - b - 5) := by
    have h3 : a - b - 5 < 0 := by
      have hb' : b > 0 := hb1
      have ha' : a < 0 := ha
      linarith
    rw [abs_of_neg h3]

  rw [h1, h2]
  ring