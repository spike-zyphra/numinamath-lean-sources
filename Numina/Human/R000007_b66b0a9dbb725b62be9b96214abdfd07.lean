import Mathlib

open Real

/- The value of \((\sqrt{169} - \sqrt{25})^2\) is:
(A) 64
(B) 8
(C) 16
(D) 144
(E) 12-/
theorem algebra_4019 : (sqrt 169 - sqrt 25)^2 = 64 := by
  --  Calculate \(\sqrt{169}\):
  --  \[
  --  \sqrt{169} = 13
  --  \]
  have h1 : sqrt 169 = 13 := by
    rw [show (169 : ℝ) = 13 * 13 by norm_num]
    exact sqrt_mul_self <| by norm_num
  -- Calculate \(\sqrt{25}\):
  --  \[
  --  \sqrt{25} = 5
  --  \]
  have h2 : sqrt 25 = 5 := by
    rw [show (25 : ℝ) = 5 * 5 by norm_num]
    exact sqrt_mul_self <| by norm_num
  -- Substitute these values back into the expression:
  --  \[
  --  (\sqrt{169} - \sqrt{25})^2 = (13 - 5)^2
  --  \]
  rw [h1, h2]
  -- Square the result:
  --  \[
  --  8^2 = 64
  --  \]
  norm_num
