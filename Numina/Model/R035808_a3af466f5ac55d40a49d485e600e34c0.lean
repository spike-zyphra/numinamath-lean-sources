import Mathlib

theorem inequalities_6375 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ((b + c) * b * c / (a ^ 2 + b * c) + (a + c) * a * c / (b ^ 2 + a * c) +
     (a + b) * a * b / (c ^ 2 + a * b)) ≥ a + b + c := by

  have h1 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc

  have h2 : a ^ 2 + b * c > 0 := by
    positivity

  have h3 : b ^ 2 + a * c > 0 := by
    positivity

  have h4 : c ^ 2 + a * b > 0 := by
    positivity

  have h5 : ((b + c) * b * c / (a ^ 2 + b * c) + (a + c) * a * c / (b ^ 2 + a * c) +
    (a + b) * a * b / (c ^ 2 + a * b)) - (a + b + c) ≥ 0 := by
    have h6 : 0 < (a ^ 2 + b * c) * (b ^ 2 + a * c) * (c ^ 2 + a * b) := by
      positivity
    have h7 : ((b + c) * b * c / (a ^ 2 + b * c) + (a + c) * a * c / (b ^ 2 + a * c) +
      (a + b) * a * b / (c ^ 2 + a * b) ) - (a + b + c) =
      ((b + c) * b * c * (b ^ 2 + a * c) * (c ^ 2 + a * b) + 
        (a + c) * a * c * (a ^ 2 + b * c) * (c ^ 2 + a * b) + 
        (a + b) * a * b * (a ^ 2 + b * c) * (b ^ 2 + a * c) - 
        (a + b + c) * (a ^ 2 + b * c) * (b ^ 2 + a * c) * (c ^ 2 + a * b)) / 
      ((a ^ 2 + b * c) * (b ^ 2 + a * c) * (c ^ 2 + a * b)) := by
      field_simp
      <;> ring
    rw [h7] at *
    apply div_nonneg
    · nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
        sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
        sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
        mul_pos (show 0 < a * b from by nlinarith) (show 0 < b * c from by nlinarith),
        mul_pos (show 0 < a * b from by nlinarith) (show 0 < a * c from by nlinarith),
        mul_pos (show 0 < b * c from by nlinarith) (show 0 < a * c from by nlinarith)]
    · positivity
  linarith