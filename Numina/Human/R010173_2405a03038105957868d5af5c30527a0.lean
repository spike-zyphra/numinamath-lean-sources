import Mathlib

/- Find $\lfloor |-4.2| \rfloor + |\lfloor -4.2 \rfloor|$. -/
theorem algebra_10734 : ⌊|(-4.2 : ℝ)|⌋ + |⌊(-4.2 : ℝ)⌋| = 9 := by
  have h : |(-4.2 : ℝ)| = 4.2 := by
    norm_num
  rw [h]
  norm_num
