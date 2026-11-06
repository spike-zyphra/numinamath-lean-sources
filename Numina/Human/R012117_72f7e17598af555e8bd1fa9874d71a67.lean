import Mathlib

/- Let $a, b, c$ be positive real numbers such that $a^2 + b^2 + c^2 = 3$. Prove that
$$\frac{1}{1+2ab}+\frac{1}{1+2bc}+\frac{1}{1+2ca}\ge 1$$ -/
theorem inequalities_92574 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 3) :
    1 ≤ 1 / (1 + 2 * a * b) + 1 / (1 + 2 * b * c) + 1 / (1 + 2 * c * a) := by 
  -- Ensure each product of two angular b as positive
  have h₁ : 0 < a * b := mul_pos ha hb
  have h₂ : 0 < b * c := mul_pos hb hc
  have h₃ : 0 < c * a := mul_pos hc ha
  -- Apply a symmetry within positive regions
  field_simp [h₁, h₂, h₃]
  -- Rearrange and check handling balances algebraically second enorm
  rw [le_div_iff (by positivity)]
  --ivariate fun parties express handle try conditions deeply
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    mul_nonneg (h₁.le) (h₂.le), mul_nonneg (h₂.le) (h₃.le), mul_nonneg (h₃.le) (h₁.le)]