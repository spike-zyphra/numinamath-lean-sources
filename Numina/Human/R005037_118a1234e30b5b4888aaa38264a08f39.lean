import Mathlib

/- Given positive real numbers $a, b, c, d$ that satisfy equalities

$$
a^{2}+d^{2}-a d=b^{2}+c^{2}+b c \quad \text { and } \quad a^{2}+b^{2}=c^{2}+d^{2}
$$

find all possible values of the expression $\frac{a b+c d}{a d+b c}$.

Answer: $\frac{\sqrt{3}}{2}$. -/
theorem trial (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (h₁ : a ^ 2 + d ^ 2 - a * d = b ^ 2 + c ^ 2 + b * c) (h₂ : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2) :
  (a * b + c * d) / (a * d + b * c) = √3 / 2 := by
  -- It suffices to prove that (a * b + c * d) ^ 2 * 4 = (a * d + b * c) ^ 2 * 3.
  suffices H : (a * b + c * d) ^ 2 * 4 = (a * d + b * c) ^ 2 * 3 by
    rw [← sq_eq_sq₀ (by positivity) (by positivity)]
    field_simp
    linear_combination H
  -- It comes from a linear combination of the given equalities.
  linear_combination
    (2 * b ^ 2 - b * c - a * d - 2 * d ^ 2) * h₁ +
      (2 * b ^ 2 + b * c + a * d - 2 * d ^ 2) * h₂
