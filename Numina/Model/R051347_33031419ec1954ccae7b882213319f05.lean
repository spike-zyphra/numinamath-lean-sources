import Mathlib

theorem inequalities_73888 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    1 / ((1 / a) + (1 / b)) + 1 / ((1 / c) + (1 / d)) ≤
    1 / ((1 / (a + c)) + (1 / (b + d))) := by
  have h1 : 1 / ((1 / a) + (1 / b)) = a * b / (a + b) := by field_simp <;> ring_nf <;> field_simp
  have h2 : 1 / ((1 / c) + (1 / d)) = c * d / (c + d) := by field_simp <;> ring_nf <;> field_simp
  have h3 : 1 / ((1 / (a + c)) + (1 / (b + d))) = (a + c) * (b + d) / (a + b + c + d) := by 
    field_simp
    <;> ring_nf
    <;> field_simp
    <;> ring_nf
  rw [h1, h2, h3]
  have pos1 : 0 < a := ha
  have pos2 : 0 < b := hb
  have pos3 : 0 < c := hc
  have pos4 : 0 < d := hd
  have pos5 : 0 < a + b := by linarith
  have pos6 : 0 < c + d := by linarith
  have pos7 : 0 < a + b + c + d := by linarith
  have h9 : a * b / (a + b) + c * d / (c + d) ≤ (a + c) * (b + d) / (a + b + c + d) := by
    -- Proof of the inequality.
    have pos6 : 0 < a * b := by nlinarith
    have pos7 : 0 < c * d := by nlinarith
    have pos8 : 0 < (a + b) * (c + d) := by nlinarith
    have pos9 : 0 < (a + b + c + d) := by linarith
    -- Use Cauchy-Schwarz or algebraic simplification
    have h10 : a * b / (a + b) + c * d / (c + d) - (a + c) * (b + d) / (a + b + c + d) ≤ 0 := by
      have h3 : (a * b / (a + b) + c * d / (c + d) - (a + c) * (b + d) / (a + b + c + d)) =
        (a * b * (c + d) * (a + b + c + d) + c * d * (a + b) * (a + b + c + d) - (a + c) * (b + d) * (a + b) * (c + d)) / ((a + b) * (c + d) * (a + b + c + d)) := by
        field_simp
        ring
      rw [h3]
      -- establish that numerator is ≤ 0
      have h13 : a * b * (c + d) * (a + b + c + d) + c * d * (a + b) * (a + b + c + d) - (a + c) * (b + d) * (a + b) * (c + d) ≤ 0 := by
        nlinarith [sq_nonneg (a * d - b * c), sq_nonneg (a * b - c * d), sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg (a + b - c - d), sq_nonneg (a * d - b * c), 
                  mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, mul_pos (show 0 < a * b by nlinarith) (show 0 < c * d by nlinarith)]
      have h30 : (a + b) * (c + d) * (a + b + c + d) > 0 := by positivity
      have h7 : (a * b * (c + d) * (a + b + c + d) + c * d * (a + b) * (a + b + c + d) - (a + c) * (b + d) * (a + b) * (c + d)) / ((a + b) * (c + d) * (a + b + c + d)) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        linarith
        nlinarith
      linarith
    linarith
  linarith