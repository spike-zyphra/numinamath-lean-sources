import Mathlib

/-
Let $ a,b,c>0$. Prove that:

$ \dfrac{a}{2a\plus{}b}\plus{}\dfrac{b}{2b\plus{}c}\plus{}\dfrac{c}{2c\plus{}a}\leq 1$
-/
theorem inequalities_52697 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (2 * a + b) + b / (2 * b + c) + c / (2 * c + a) ≤ 1 := by
  -- Some positivity auxillary lemmas.
  have h_pos1 : 2 * a + b > 0 := by nlinarith
  have h_pos2 : 2 * b + c > 0 := by nlinarith
  have h_pos3 : 2 * c + a > 0 := by nlinarith
  have h : a / (2 * a + b) + b / (2 * b + c) + c / (2 * c + a) ≤ 1 := by
    -- Sub 1 to the left hand side.
    have h1 : a / (2 * a + b) + b / (2 * b + c) + c / (2 * c + a) - 1 ≤ 0 := by
      -- Caculate the common denominator of the left hand side.
      have h2 : a / (2 * a + b) + b / (2 * b + c) + c / (2 * c + a) - 1 = 
        (a * (2 * b + c) * (2 * c + a) + b * (2 * c + a) * (2 * a + b) + c * (2 * a + b) * (2 * b + c) - 
        (2 * a + b) * (2 * b + c) * (2 * c + a)) / 
        ((2 * a + b) * (2 * b + c) * (2 * c + a)) := by
        field_simp
        ring
      rw [h2]
      have h3 : (2 * a + b) * (2 * b + c) * (2 * c + a) > 0 := by
        apply mul_pos
        apply mul_pos
        all_goals nlinarith
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Prove numerator ≤ 0
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      · -- Prove denominator ≥ 0
        nlinarith
    linarith
  linarith