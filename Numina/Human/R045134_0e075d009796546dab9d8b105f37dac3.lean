import Mathlib

/- Given that $a^{2}+b^{2}+(a+b)^{2}=c^{2}+d^{2}+(c+d)^{2}$, prove that $a^{4}+b^{4}+(a+b)^{4}=c^{4}+d^{4}+(c+d)^{4}$. -/
theorem algebra_240720 {a b c d : ℝ} (h : a ^ 2 + b ^ 2 + (a + b) ^ 2 = c ^ 2 + d ^ 2 + (c + d) ^ 2) :
    a ^ 4 + b ^ 4 + (a + b) ^ 4 = c ^ 4 + d ^ 4 + (c + d) ^ 4 := by
  -- Simply square both sides of h.
  replace h := congr_arg (· ^ 2) h
  simp at h
  linarith