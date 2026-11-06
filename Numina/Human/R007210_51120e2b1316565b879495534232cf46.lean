import Mathlib

/-The ratio $\frac{10^{2000}+10^{2002}}{10^{2001}+10^{2001}}$ is closest to which whole number?-/
theorem algebra_12197 : round ((10^2000 + 10^2002 : ℝ) / (10^2001 + 10^2001 : ℝ)) = 5 := by
  -- We have $$
  -- \frac{10^{2000} + 10^{2002}}{10^{2001} + 10^{2001}}=
  -- \frac{{10^{2000}(1 + 100)}}{{10^{2000}(10 + 10)}} = \frac{101}{20}\approx \boxed{5}.
  -- $$
  have : (10 ^ 2000 + 10 ^ 2002 : ℝ) = 10 ^ 2000 * (1 + 100) := by linarith
  rw [this]
  have : (10 ^ 2001 + 10 ^ 2001 : ℝ) = 10 ^ 2000 * (10 + 10) := by linarith
  rw [this]
  norm_num
  rw [round]
  have : Int.fract ((101 / 20 : ℝ)) = 1/20 := by
    rw [Int.fract]
    have : (⌊101 / (20 : ℝ)⌋ : ℝ) = 5 := by norm_num
    rw [this]
    linarith
  rw [this]
  split
  . norm_num
  . linarith
