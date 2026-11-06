import Mathlib
/- If $4^{4^{4}}=\sqrt[ 128]{2^{2^{2^{n}}}}$, find $n$. -/
theorem inequalities_609060 (n : ℕ) (h : (4 : ℝ) ^ 4 ^ 4 = (((2 : ℝ) ^ 2 ^ 2 ^ n)) ^ ((1 : ℝ) / 128)) : n = 4:= by

  -- Helper lemma: If 2^x = 2^y, then x = y (using logarithm properties)
  have h1 : ∀ x y : ℝ, (2 : ℝ) ^ x = 2 ^ y → x = y:= by
    intro x y h
    replace h : Real.logb 2 ((2 : ℝ) ^ x) = Real.logb 2 (2 ^ y) := by rw [h]
    simp at h
    exact h

  -- Rewrite 4^(4^4) as (2^2)^(4^4)
  have h2 : (4 : ℝ) ^ 4 ^ 4 = (2 ^ 2) ^ 4 ^ 4:= by ring_nf

  -- Simplify the left side of the equation using exponent laws
  rw [show ((2 : ℝ) ^ 2) ^ 4 ^ 4 = (2 : ℝ) ^ (2 * 4 ^ 4) by ring_nf] at h2

  -- Convert integer exponents to real numbers
  rw [show (2 : ℝ) ^ 2 ^ 2 ^ n = 2 ^ (2 ^ 2 ^ n : ℝ) by norm_cast] at h

  -- Apply the property of real power multiplication
  rw [Eq.symm (Real.rpow_mul (by positivity) (2 ^ 2 ^ n) (1 / 128))] at h

  -- Substitute the simplified left side
  rw [h2] at h

  -- Convert integer multiplication to real multiplication
  rw [show (2 : ℝ) ^ (2 * 4 ^ 4) = (2 : ℝ) ^ (2 * 4 ^ 4 : ℝ) by ring_nf] at h

  -- Apply the helper lemma to equate exponents
  replace h:= h1 (2 * 4 ^ 4) (2 ^ 2 ^ n * (1 / 128)) h

  -- Simplify the equation using arithmetic
  replace h : (2 : ℝ) ^ 8 * 4 ^ 4 = 2 ^ 2 ^ n:= by linarith
  replace h : (2 : ℝ) ^ 16 = 2 ^ 2 ^ n:= by linarith

  -- Convert more integer exponents to real numbers
  rw [show (2 : ℝ) ^ 16 = 2 ^ (16 : ℝ) by norm_cast] at h
  rw [show (2 : ℝ) ^ 2 ^ n = 2 ^ (2 ^ n : ℝ) by norm_cast] at h

  -- Apply helper lemma again to equate exponents
  replace h:= h1 (16 : ℝ) (2 ^ n : ℝ) h

  -- Further simplification
  replace h : (2 : ℝ) ^ 4 = 2 ^ n:= by linarith

  -- Final conversions and application of helper lemma
  rw [show (2 : ℝ) ^ 4 = 2 ^ (4 : ℝ) by norm_cast] at h
  rw [show (2 : ℝ) ^ n = 2 ^ (n : ℝ) by norm_cast] at h
  replace h:= h1 4 n h

  -- Complete the proof using arithmetic
  rify
  linarith
