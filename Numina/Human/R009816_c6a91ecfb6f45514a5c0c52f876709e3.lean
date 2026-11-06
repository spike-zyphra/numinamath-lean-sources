import Mathlib

/-Find $2^x$ if

\begin{align*}
2^x+3^y&=5,\\
2^{x+2}+3^{y+1} &=18.
\end{align*}-/
theorem algebra_10683 {x y : ℝ} (eq₁ : (2 : ℝ) ^ x + 3 ^ y = 5) (eq₂ : (2 : ℝ) ^ (x + 2) + 3 ^ (y + 1) = 18) : (2 : ℝ) ^ x = 3 := by
  -- subsitute a = 2 ^ x, b = 3 ^ y
  set a := (2 : ℝ) ^ x with ha
  set b := (3 : ℝ) ^ y with hb
  repeat rw [Real.rpow_add] at eq₂
  rw [<-ha, <-hb] at eq₂
  ring_nf at eq₂
  -- substract two equation
  calc
    a = (a * 4 + b * 3) - 3 * (a + b) := by ring_nf
    _ = 18 - 3 * 5 := by rw [eq₁, eq₂]
    _ = 3 := by norm_num
  repeat positivity
