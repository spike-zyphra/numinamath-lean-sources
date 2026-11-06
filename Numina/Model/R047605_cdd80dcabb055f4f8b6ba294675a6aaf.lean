import Mathlib

open Real Set
open scoped Topology

theorem inequalities_108946 :
  ∀ x : ℝ, x ∈ Ici 0 → x^3 - 3 * x + 2 ≥ 0 ∧
  (∀ a b c : ℝ, a > 0 → b > 0 → c > 0 →
    (1 / a + 1 / b + 1 / c ≤ 3) → (a^2 + b^2 + c^2 ≥ 3)) := by
  intro x hx
  constructor
  · -- First part: show $x^3 - 3x + 2 \geq 0$ for all $x \in [0, \infty)$
    have h1 : x ≥ 0 := hx
    have h2 : x ^ 3 - 3 * x + 2 = (x - 1) ^ 2 * (x + 2) := by
      nlinarith
    have h3 : (x - 1) ^ 2 ≥ 0 := by
      apply sq_nonneg
    have h4 : x + 2 ≥ 2 := by
      linarith
    have h5 : (x - 1) ^ 2 * (x + 2) ≥ 0 := by
      positivity
    linarith [h2, h5]
  · -- Second part: show if $a, b, c \in (0, \infty)$ and $\frac{1}{a} + \frac{1}{b} + \frac{1}{c} \le 3$ then $a^2 + b^2 + c^2 \ge 3$
    intro a b c ha hb hc h1
    have h3 : a * b + b * c + c * a ≤ 3 * a * b * c := by
      have h3 : 1 / a + 1 / b + 1 / c ≤ 3 := by
        linarith
      have h4 : 1 / a + 1 / b + 1 / c = (b * c + a * c + a * b) / (a * b * c) := by
        field_simp
        <;> ring
      rw [h4] at h3
      have h5 : a * b * c > 0 := by
        positivity
      have h6 : b * c + a * c + a * b ≤ 3 * (a * b * c) := by 
        have h7 : (b * c + a * c + a * b) / (a * b * c) ≤ (3 : ℝ) := by
          linarith
        have h8 : (b * c + a * c + a * b) ≤ 3 * (a * b * c) := by 
          have h9 : (b * c + a * c + a * b) = ( (b * c + a * c + a * b) / (a * b * c) ) * (a * b * c) := by 
            field_simp 
            <;> nlinarith 
          nlinarith [h7, show 0 < a * b * c by positivity]
        linarith
      linarith
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]