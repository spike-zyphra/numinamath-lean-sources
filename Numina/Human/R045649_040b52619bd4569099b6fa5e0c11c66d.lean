import Mathlib

/- William Sydney Porter tried to perform the calculation $\frac{-3+4i}{1+2i}$. However, he accidentally missed the minus sign, finding $\frac{3+4i}{1+2i}=\frac{11}{5}-\frac{2}{5}i$. What answer should he have obtained? -/
theorem algebra_20610 : (-3 + 4 * Complex.I) / (1 + 2 * Complex.I) = 1 + 2 * Complex.I := by
  -- 只需证明 (-3 + 4 * Complex.I) = (1 + 2 * Complex.I) *（1 + 2 * Complex.I）
  have h1 : (1 + 2 * Complex.I) ≠ (0 : ℂ):= by
    by_contra!
    replace this : (1 + 2 * Complex.I).re = (0 : ℂ).re:= by rw [this]
    norm_num at this
  field_simp
  ring_nf
  norm_num
  ring_nf
