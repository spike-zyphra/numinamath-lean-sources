import Mathlib

open Real

theorem inequalities_84236 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a + b < 2) :
    1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) ≤ 2 / (1 + a * b) ∧
    (1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) = 2 / (1 + a * b) ↔ a = b ∧ b < 1) := by

  have h1 : 0 < a * b := by
    nlinarith
  have h2 : a * b < 1 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2), mul_pos ha hb]

  constructor
  · -- Prove that $\frac{1}{1+a^2}+\frac{1}{1+b^2} \le \frac{2}{1+ab}$
    have h3 : (1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) ) - (2 / (1 + a * b) ) ≤ 0 := by

      have pos1 : 0 < (1 + a ^ 2) := by
        nlinarith
      have pos2 : 0 < (1 + b ^ 2) := by
        nlinarith
      have pos3 : 0 < (1 + a * b) := by
        nlinarith [ha, hb]

      have h4 : (1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) ) - (2 / (1 + a * b) ) =
          ( (1 + b^2) * (1 + a * b) + (1 + a^2) * (1 + a * b) - 2 * (1 + a^2) * (1 + b^2) ) / ( (1 + a^2) * (1 + b^2) * (1 + a * b) ) := by
        field_simp
        ring

      rw [h4]

      have h5 : ( (1 + b^2) * (1 + a * b) + (1 + a^2) * (1 + a * b) - 2 * (1 + a^2) * (1 + b^2) ) ≤ 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - 1), sq_nonneg (a + b - 2), 
                  h2, mul_pos ha hb, mul_pos ha (show 0 < b by linarith)
                ]

      have h6 : (1 + a^2) * (1 + b^2) * (1 + a * b) > 0 := by
        positivity

      apply div_nonpos_of_nonpos_of_nonneg h5 (show (1 + a^2) * (1 + b^2) * (1 + a * b) ≥ 0 by linarith)
    linarith

  · -- Prove that $ \frac{1}{1+a^2}+\frac{1}{1+b^2} = \frac{2}{1+ab} \leftrightarrow a = b ∧ b < 1 $
    constructor
    · -- Forward: if $ \frac{1}{1+a^2}+\frac{1}{1+b^2} = \frac{2}{1+ab} $ then $a = b ∧ b < 1$
      intro heq

      have pos1 : 0 < (1 + a ^ 2) := by
        nlinarith
      have pos2 : 0 < (1 + b ^ 2) := by
        nlinarith
      have pos3 : 0 < (1 + a * b) := by
        nlinarith [ha, hb]

      have heq2 : (1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) ) = (2 / (1 + a * b) ) := by linarith [heq]

      have heq3 : (1 + b^2) * (1 + a * b) + (1 + a^2) * (1 + a * b) = 2 * (1 + a^2) * (1 + b^2) := by
        field_simp [pos1, pos2, pos3] at heq2 ⊢
        nlinarith

      have heq4 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - 1), sq_nonneg (a + b - 2), 
                  h2, mul_pos ha hb, mul_pos ha (show 0 < b by linarith)
                ]

      have h6 : a = b := by
        nlinarith [pow_eq_zero heq4]

      have hb2 : b < 1 := by
        nlinarith [show a * b < 1 by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2), h2], h, h6
        ]

      constructor
      · -- Show that $a = b$
        linarith [h6]
      · -- Show that $b < 1$
        linarith [hb2]

    · -- Backward: if $ a = b ∧ b < 1 $ then $ \frac{1}{1+a^2}+\frac{1}{1+b^2} = \frac{2}{1+ab} $ 
      rintro ⟨ha_eq, hb_lt⟩

      have h10 : a = b := by linarith [ha_eq]

      rw [show b = a by linarith [h10] ]

      field_simp [show 0 < a by linarith, show 0 < a * a by nlinarith]
      nlinarith [ sq_nonneg (a - 1), sq_nonneg (a ^ 2 - 1), h, h10, hb_lt
      ]