import Mathlib

open Real

/-
Let \( a, b, c \) be positive real numbers such that \( a b c = 1 \).
Prove that:
\[
\frac{a b}{a^{5}+b^{5}+a b}+\frac{b c}{b^{5}+c^{5}+b c}+\frac{c a}{c^{5}+a^{5}+c a} \leq 1.
\]
When does equality hold?
-/

theorem Algebra_24661 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a * b / (a ^ 5 + b ^ 5 + a * b) +
    b * c / (b ^ 5 + c ^ 5 + b * c) +
    c * a / (c ^ 5 + a ^ 5 + c * a) ≤ 1 := by
  /-
  We have:
  \[
  a^{5}+b^{5}-a^{2} b^{2}(a+b)=(a^{3}-b^{3})(a^{2}-b^{2}) \geq 0,
  \]
  which implies:
  \[
  a^{5}+b^{5} \geq a^{2} b^{2}(a+b).
  \]
  -/
  have h1 : ∀ a > (0 : ℝ), ∀ b > (0 : ℝ), ∀ c > (0 : ℝ), a ^ 5 + b ^ 5 ≥ a ^ 2 * b ^ 2 * (a + b) := by
    intro a ha b hb c hc
    have h : (a ^ 3 - b ^ 3) * (a ^ 2 - b ^ 2) ≥ 0 := by
      by_cases hab : a ≥ b
      . have : a ^ 2 ≥ b ^ 2 := by nlinarith
        have : a ^ 3 ≥ b ^ 3 := by nlinarith
        nlinarith
      . have : a ^ 2 < b ^ 2 := by nlinarith
        have : a ^ 3 < b ^ 3 := by nlinarith
        nlinarith
    linarith
  /-
  Hence, we obtain:
  \[
  \frac{a b}{a^{5}+b^{5}+a b} \leq \frac{a b}{a^{2} b^{2}(a+b)+a b}.
  \]
  Rewriting in terms of \( c \), using \( a b c = 1 \), we get:
  \[
  \frac{a b}{a^{5}+b^{5}+a b} \leq \frac{c}{a+b+c}.
  \]
  -/
  have h2 : ∀ a > (0 : ℝ), ∀ b > (0 : ℝ), ∀ c > (0 : ℝ), a * b * c = 1 → a * b / (a ^ 5 + b ^ 5 + a * b) ≤ c / (a + b + c) := by
    intro a ha b hb c hc habc
    specialize h1 a ha b hb c hc
    calc
      _ ≤ a * b / (a ^ 2 * b ^ 2 * (a + b) + a * b) := by gcongr
      _ = (a * b * c) * c / ((a * b * c) ^ 2 * (a + b) + (a * b * c) * c) := by field_simp; ring
      _ = _ := by field_simp [habc]

  have h2a := h2 a ha b hb c hc habc

  /-
  Similarly, applying the same reasoning cyclically to the other terms:
  \[
  \frac{b c}{b^{5}+c^{5}+b c} \leq \frac{a}{a+b+c},
  \]
  \[
  \frac{c a}{c^{5}+a^{5}+c a} \leq \frac{b}{a+b+c}.
  \]
  -/
  have h2b : b * c / (b ^ 5 + c ^ 5 + b * c) ≤ a / (a + b + c) := by
    have := h2 b hb c hc a ha (by linarith)
    ring_nf at this ⊢
    assumption

  have h2c : c * a / (c ^ 5 + a ^ 5 + c * a) ≤ b / (a + b + c) := by
    have := h2 c hc a ha b hb (by linarith)
    ring_nf at this ⊢
    assumption

  /-
  Summing these inequalities, we get:
  \[
  \frac{a b}{a^{5}+b^{5}+a b} + \frac{b c}{b^{5}+c^{5}+b c} + \frac{c a}{c^{5}+a^{5}+c a}
  \leq \frac{c}{a+b+c} + \frac{a}{a+b+c} + \frac{b}{a+b+c} = 1.
  \]
  -/
  have h3 : c / (a + b + c) + a / (a + b + c) + b / (a + b + c) = 1 := by
    field_simp
    ring

  have sum_ineq : a * b / (a ^ 5 + b ^ 5 + a * b) + b * c / (b ^ 5 + c ^ 5 + b * c) +
    c * a / (c ^ 5 + a ^ 5 + c * a) ≤ 1 := by
    calc
      a * b / (a ^ 5 + b ^ 5 + a * b) + b * c / (b ^ 5 + c ^ 5 + b * c) + c * a / (c ^ 5 + a ^ 5 + c * a)
        ≤ c / (a + b + c) + a / (a + b + c) + b / (a + b + c) := by linarith
      _ = 1 := h3
  /-
  Equality holds if and only if \( a = b = c \).
  -/
  exact sum_ineq
