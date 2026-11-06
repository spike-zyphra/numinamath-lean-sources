import Mathlib

/- Given that $\frac{a}{25-a}+\frac{b}{65-b}+\frac{c}{60-c}=7$, evaluate $\frac{5}{25-a}+\frac{13}{65-b}+\frac{12}{60-c}$. -/
theorem algebra_14475 {a b c : ℝ} (ha : a ≠ 25) (hb : b ≠ 65) (hc : c ≠ 60)
    (h : a / (25 - a) + b / (65 - b) + c / (60 - c) = 7) :
    5 / (25 - a) + 13 / (65 - b) + 12 / (60 - c) = 2 := by 
  field_simp [sub_ne_zero.2 ha.symm, sub_ne_zero.2 hb.symm, sub_ne_zero.2 hc.symm] at h ⊢
  linarith