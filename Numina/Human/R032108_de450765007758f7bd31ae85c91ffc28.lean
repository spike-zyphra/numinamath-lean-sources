import Mathlib

open Real Set
open scoped BigOperators

/- Find the minimum of the function
\[\frac{xy}{x^2 + y^2}\]in the domain $\frac{2}{5} \le x \le \frac{1}{2}$ and $\frac{1}{3} \le y \le \frac{3}{8}.$ -/
theorem algebra_15897 :
  IsLeast {t : ℝ | ∃ x y, x ∈ Icc (2/5) (1/2) ∧ y ∈ Icc (1/3) (3/8) ∧ t = x * y / (x ^ 2 + y ^ 2)} (6/13) := by
  refine' ⟨⟨1/2, 1/3, by norm_num [Icc_def]⟩, _⟩
  rintro t ⟨x, y, hx, hy, rfl⟩
  norm_num [Icc_def] at hx hy ⊢
  have h1 : 0 < x ^ 2 + y ^ 2 := by nlinarith
  have h2 : 0 < x * y := by nlinarith
  rw [div_le_div_iff] <;> nlinarith