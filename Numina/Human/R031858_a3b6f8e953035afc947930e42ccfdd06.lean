import Mathlib

/- Let $a,b$ be positive real numbers such that $b^3+b\le a-a^3$. Prove that:
i) $b<a<1$
ii) $a^2+b^2<1$ -/
theorem inequalities_37789 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : b^3 + b ≤ a - a^3) :
    b < a ∧ a < 1 ∧ a^2 + b^2 < 1 := by
  have hb2 : 0 < b^2 := by nlinarith
  have ha2 : 0 < a^2 := by nlinarith
  have h1 : b < a := by nlinarith
  have h2 : a < 1 := by nlinarith
  have h3 : a^2 + b^2 < 1 := by nlinarith
  exact ⟨h1, h2, h3⟩