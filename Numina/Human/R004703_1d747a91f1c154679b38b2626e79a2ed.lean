import Mathlib

/-Let $a, b, c$ be positive real numbers, and $a+b+c=1$. Prove:
$$
\left(a^{2}+b^{2}+c^{2}\right)\left(\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}\right) \geqslant \frac{1}{2} .
$$-/
theorem inequalities_305663 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    (a^2 + b^2 + c^2) * (a / (b + c) + b / (c + a) + c / (a + b)) ≥ 1 / 2 := by
  -- Establish a lower bound for the sum of squares using the Cauchy-Schwarz inequality.
  have h1 : a ^ 2 + b ^ 2 + c ^ 2 ≥ 1 / 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), h]
  
  have h2 : a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
    -- Verify that the denominators are positive.
    have hbc : b + c > 0 := by nlinarith
    have hca : c + a > 0 := by nlinarith
    have hab : a + b > 0 := by nlinarith

    have h2' : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
      -- Use field simplification to handle division in inequalities.
      have h1 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
          (2 * a * (c + a) * (a + b) + 2 * b * (a + b) * (b + c) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b)) /
          (2 * (b + c) * (c + a) * (a + b)) := by
        field_simp
        ring

      -- Show the numerator is non-negative using polynomial expansion.
      have h2 : 2 * a * (c + a) * (a + b) + 2 * b * (a + b) * (b + c) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b) ≥ 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b + c - 1), h]

      have h3 : 2 * (b + c) * (c + a) * (a + b) > 0 := by
        apply mul_pos
        apply mul_pos
        · linarith
        · nlinarith
        · nlinarith
      
      -- Conclude via arithmetic manipulation.
      have h4 : (2 * a * (c + a) * (a + b) + 2 * b * (a + b) * (b + c) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b)) / (2 * (b + c) * (c + a) * (a + b)) ≥ 0 := by
        apply div_nonneg
        · linarith
        · nlinarith

      linarith [h1, h4]
    
    linarith
  -- Combine the results of the two inequalities to prove the final result.
  nlinarith [h1, h2]