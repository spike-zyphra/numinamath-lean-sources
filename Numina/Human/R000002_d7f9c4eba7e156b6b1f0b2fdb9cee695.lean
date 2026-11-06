import Mathlib

/- Calculate the sum of the coefficients of \( P(x) \) if \( \left(20 x^{27} + 2 x^{2} + 1\right) P(x) = 2001 x^{2001} \).-/
theorem algebra_4014 {P : ℝ → ℝ} (hp : ∀ x, (20*x^27+2*x^2+1)* P x = 2001 * x^2001) :
    P 1 = 87 := by
  -- Substitute \( x = 1 \) into the equation:
  --  \[
  --  (20 \cdot 1^{27} + 2 \cdot 1^{2} + 1) P(1) = 2001 \cdot 1^{2001}
  --  \]
  have := hp 1
  --  Simplifying the terms inside the parentheses:
  --  \[
  --  (20 \cdot 1 + 2 \cdot 1 + 1) P(1) = 2001
  --  \]
  --  \[
  --  (20 + 2 + 1) P(1) = 2001
  --  \]
  --  \[
  --  23 P(1) = 2001
  --  \]
  simp at this
  rw [show 20 + 2 + 1 = (23 : ℝ) by ring] at this
  rw [show (2001 : ℝ) = 23 * 87 by norm_num] at this
  -- To find \( P(1) \), divide both sides of the equation by 23:
  --  \[
  --  P(1) = \frac{2001}{23}
  --  \]
  rw [mul_right_inj' (by norm_num)] at this
  exact this
