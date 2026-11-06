import Mathlib

open Real

/- Prove that for all real $x, y$

$$
\frac{x+y}{x^{2}-x y+y^{2}} \leq \frac{2 \sqrt{2}}{\sqrt{x^{2}+y^{2}}}
$$ -/
theorem inequalities_606254 (x y : ℝ) (h : x^2 + y^2 ≠ 0) :
  (x + y) / (x ^ 2 - x * y + y ^ 2) ≤ 2 * sqrt 2 / sqrt (x ^ 2 + y ^ 2) := by 
    -- The inequality rewrites as
    -- $$ \frac{x+y}{x^{2}-x y+y^{2}} \leq \frac{\sqrt{2\left(x^{2}+y^{2}\right)}}{\frac{x^{2}+y^{2}}{2}} $$
    have h3 : 2 * √2 / √(x^2 + y^2) = √(2 * (x^2 + y^2)) / ((x^2 +y^2) / 2) := by 
      field_simp
      ring_nf
      rw [sq_sqrt (by positivity)]
      linarith
    rw [h3]
    
    -- Now it is enough to prove the next two simple inequalities:

    -- $$ x+y \leq \sqrt{2\left(x^{2}+y^{2}\right)}, \quad x^{2}-x y+y^{2} \geq \frac{x^{2}+y^{2}}{2} $$
    have h1 : x + y ≤ (2 * (x^2 + y^2)).sqrt := by 
      by_cases h2 : x + y < 0 
      · suffices 0 ≤  √(2 * (x ^ 2 + y ^ 2)) by linarith
        positivity
      · simp at h2
        apply (Real.le_sqrt h2 (by positivity)).2 
        linarith [two_mul_le_add_sq x y]
    have h2 : x^2 - x* y + y^2 ≥ (x^2 + y^2) / 2 := by 
      linarith [two_mul_le_add_sq x y]
    apply div_le_div₀ 
    all_goals first | assumption | positivity