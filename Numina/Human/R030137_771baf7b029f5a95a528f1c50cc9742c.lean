import Mathlib
/- What is the 18 th digit after the decimal point of $\frac{10000}{9899}$ ? -/
theorem number_theory_610952 : ⌊10000 / (9899 : ℝ) * 10 ^ 18⌋ ≡ 5 [ZMOD 10]:= by
  -- First, we calculate the decimal expansion of 10000 / 9899
  norm_num
  -- Then, we find the 18th digit after the decimal point
  rfl