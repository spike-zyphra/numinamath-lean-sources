import Mathlib

theorem algebra_318989 {a b : ℝ} (ha : a < 0) (hb : b < 0) (h : a < b) (h' : a / b + b / a = 6) :
    ((a + b) / (a - b))^3 = 2 * Real.sqrt 2 := by
  have h1 : a * b > 0 := by
    have ha1 : a < 0 := ha
    have hb1 : b < 0 := hb
    nlinarith
  have h2 : a ^ 2 + b ^ 2 = 6 * (a * b) := by
    have h3 : a / b + b / a = 6 := h'
    have h4 : a / b + b / a = (a ^ 2 + b ^ 2) / (a * b) := by
      field_simp [(show b ≠ 0 by linarith), (show a ≠ 0 by linarith)]
      <;> ring
    rw [h4] at h3
    have h5 : (a ^ 2 + b ^ 2) / (a * b) = 6 := by linarith
    have h6 : a * b > 0 := h1
    have h7 : a ^ 2 + b ^ 2 = 6 * (a * b) := by
      have h8 : (a ^ 2 + b ^ 2) / (a * b) = 6 := h5
      field_simp [(show a * b > 0 by linarith)] at h8 ⊢
      <;> nlinarith
    nlinarith
  have h3 : ((a + b) / (a - b)) ^ 2 = 2 := by
    have h4 : a - b < 0 := by linarith
    have h5 : ((a + b) / (a - b)) ^ 2 = ((a + b) ^ 2) / ((a - b) ^ 2) := by
      field_simp [(show a - b ≠ 0 by linarith)]
    rw [h5]
    have h6 : (a + b) ^ 2 = 8 * (a * b) := by
      nlinarith [h2, sq_pos_of_ne_zero (show a ≠ 0 by linarith), sq_pos_of_ne_zero (show b ≠ 0 by linarith)]
    have h7 : (a - b) ^ 2 = 4 * (a * b) := by
      nlinarith [h2, sq_pos_of_ne_zero (show a ≠ 0 by linarith), sq_pos_of_ne_zero (show b ≠ 0 by linarith)]
    rw [h6, h7]
    have h8 : (8 * (a * b) : ℝ) / (4 * (a * b) : ℝ) = 2 := by
      have h9 : a * b > 0 := h1
      have h11 : 4 * (a * b) > 0 := by nlinarith
      field_simp [h11]
      <;> nlinarith
    linarith
  have h4 : ((a + b) / (a - b)) > 0 := by
    have h5 : a - b < 0 := by linarith
    have h6 : a + b < 0 := by linarith
    have h7 : (a + b) / (a - b) > 0 := by
      apply div_pos_of_neg_of_neg
      all_goals linarith
    linarith
  -- Now that we have $\left(\frac{A + b}{a - b}\right)^2 = 2$ and $\frac{A + b}{a - b} > 0$.
  -- We can write $\frac{A + b}{a - b} = \sqrt{2}$
  have h5 : ( (a + b) / (a - b) ) = Real.sqrt 2 := by
    have h4 : ( (a + b) / (a - b) ) ^ 2 = 2 := h3
    have h5 : ( (a + b) / (a - b) ) ≥ 0 := by linarith
    have h6 : Real.sqrt (( (a + b) / (a - b) ) ^ 2) = Real.sqrt 2 := by
      rw [h4]
    have h7 : Real.sqrt (( (a + b) / (a - b) ) ^ 2) = ( (a + b) / (a - b) ) := by
      rw [Real.sqrt_sq]
      linarith
    have h8 : ( (a + b) / (a - b) ) = Real.sqrt 2 := by
      nlinarith [h7, h6]
    linarith
  -- Finally, now that we have $\frac{a + b}{a - b} = \sqrt{2}$.
  -- We compute $\left(\frac{a + b}{a - b}\right)^3 = (\sqrt{2})^3 = 2\sqrt{2}$.
  calc
    ((a + b) / (a - b)) ^ 3 = ( (a + b) / (a - b) ) ^ 2 * ( (a + b) / (a - b) ) := by ring
    _ = 2 * ( (a + b) / (a - b) ) := by
      rw [h3]
    _ = 2 * Real.sqrt 2 := by
      rw [h5]