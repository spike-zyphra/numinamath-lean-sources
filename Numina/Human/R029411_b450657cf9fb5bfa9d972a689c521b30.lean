import Mathlib

/- Let $a, b, c, d, e$ be real numbers such that $a+b+c+d+e=0$. Let, also $A=a b+b c+c d+d e+e a$ and $B=a c+c e+e b+b d+d a$.
Show that
$$
2005 A+B \leq 0 \text { or } \quad A+2005 B \leq 0
$$ -/
theorem inequalities_604174 (a b c d e : ℝ) (h₀ : a + b + c + d + e = 0)
    (A B : ℝ) (hA : A = a * b + b * c + c * d + d * e + e * a)
    (hB : B = a * c + c * e + e * b + b * d + d * a) :
    2005 * A + B ≤ 0 ∨ A + 2005 * B ≤ 0 := by 
  -- We have $0=(a+b+c+d+e)^{2}=a^{2}+b^{2}+c^{2}+d^{2}+e^{2}+2 A+2 B$
  have h1: (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) + 2 * (A + B) = 0 := by
    calc 
      _ = (a + b + c + d + e) ^ 2 := by rw [hA, hB]; ring
      _ = 0 := by rw [h₀]; simp
  -- This implies that $A + B ≤ 0$
  have hA_add_B_nonpos: A + B ≤ 0 := by
    have : A + B = - ((1/2) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2)) := by linarith only [h1]
    rw [this]
    apply neg_nonpos.mpr
    positivity
  have h2: (A + 2005 * B) + (2005 * A + B) ≤ 0 := by linarith
  -- So, either $2005A + B ≤ 0$ or $A + 2005B ≤ 0$ holds as required.
  by_contra h
  simp at h
  have := add_pos h.2 h.1
  linarith