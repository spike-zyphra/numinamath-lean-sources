import Mathlib
/- 3. For positive real numbers $a, b, c, d$, prove:
$$\frac{c}{a}(8 b+c)+\frac{d}{b}(8 c+d)+\frac{a}{c}(8 d+a)+\frac{b}{d}(8 a+b) \geqslant 9(a+b+c+d),$$

with equality if and only if $a=c$ and $b=d$. -/
theorem inequalities_596997 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
c / a * (8 * b + c) + d / b * (8 * c + d) + a / c * (8 * d + a) + b / d * (8 * a + b) ≥
9 * (a + b + c + d) ∧ ((c / a * (8 * b + c) + d / b * (8 * c + d) + a / c * (8 * d + a) +
b / d * (8 * a + b) = 9 * (a + b + c + d)) ↔ a = c ∧ b = d):= by
  -- First inequality: Using AM-GM to show c/a * (8b) + a/c * (8d) ≥ 16√(bd)
  have h1 : c / a * (8 * b) + a / c * (8 * d) ≥ 16 * √(b * d):= by
    field_simp
    -- Establish that a*c > 0 for division
    have g1 : a * c > 0:= by positivity
    suffices 16 * (√b * √d) * (a * c) ≤ (c * (8 * b) * c + a * (8 * d) * a) by exact (le_div_iff₀ g1).mpr this
    -- Use the fact that (c*√b - a*√d)² ≥ 0
    have g2 : (c * √b - a * √d) ^ 2 ≥ 0:= by positivity
    ring_nf at g2
    field_simp at g2
    linarith

  -- Second inequality: Using AM-GM to show d/b * (8c) + b/d * (8a) ≥ 16√(ca)
  have h2 : d / b * (8 * c) + b / d * (8 * a) ≥ 16 * √(c * a):= by
    field_simp
    -- Establish that b*d > 0 for division
    have g1 : b * d > 0:= by positivity
    suffices 16 * (√c * √a) * (b * d) ≤ (d * (8 * c) * d + b * (8 * a) * b) by exact (le_div_iff₀ g1).mpr this
    -- Use the fact that (d*√c - b*√a)² ≥ 0
    have g2 : (d * √c - b * √a) ^ 2 ≥ 0:= by positivity
    ring_nf at g2
    field_simp at g2
    linarith

  -- Algebraic manipulation to express c/a*c + a/c*a + 16√(ca) - 9(a+c) as a non-negative expression
  have h3 : c / a * c + a / c * a + 16 * √(c * a) - 9 * (a + c) = (√a - √c) ^ 4 * (((√a + √c) ^ 2 + 2 * √a * √c) / (a * c)):= by
    rw [show √(c * a) = √c * √a by field_simp]
    -- Substituting with square roots for cleaner manipulation
    set A:= √a with hA
    set C:= √c with hC
    clear_value A C
    replace hA : a = A ^ 2:= by rw [hA] ; field_simp
    replace hC : c = C ^ 2:= by rw [hC] ; field_simp
    subst a c
    field_simp
    linarith

  -- Similar algebraic manipulation for the b,d terms
  have h4 : d / b * d + b / d * b + 16 * √(b * d) - 9 * (b + d) = (√b - √d) ^ 4 * (((√b + √d) ^ 2 + 2 * √b * √d) / (b * d)):= by
    rw [show √(b * d) = √b * √d by field_simp]
    set B:= √b with hB
    set D:= √d with hD
    clear_value B D
    replace hB : b = B ^ 2:= by rw [hB] ; field_simp
    replace hD : d = D ^ 2:= by rw [hD] ; field_simp
    subst b d
    field_simp
    linarith

  -- Establishing that the expressions are non-negative
  have h5 : (√a - √c) ^ 4 * (((√a + √c) ^ 2 + 2 * √a * √c) / (a * c)) ≥ 0:= by positivity
  have h6 : (√b - √d) ^ 4 * (((√b + √d) ^ 2 + 2 * √b * √d) / (b * d)) ≥ 0:= by positivity

  -- Proving the conjunction
  constructor
  -- First part: Proving the inequality
  .
    linarith

  -- Second part: Proving the equality condition
  .
    constructor
    -- Forward direction: Equality implies a=c and b=d
    .
      intro h
      replace h5 : (√a - √c) ^ 4 * (((√a + √c) ^ 2 + 2 * √a * √c) / (a * c)) = 0:= by linarith
      replace h6 : (√b - √d) ^ 4 * (((√b + √d) ^ 2 + 2 * √b * √d) / (b * d)) = 0:= by linarith
      -- The denominators are positive
      have g1 : ((√a + √c) ^ 2 + 2 * √a * √c) / (a * c) ≠ 0:= by positivity
      have g2 : ((√b + √d) ^ 2 + 2 * √b * √d) / (b * d) ≠ 0:= by positivity
      simp [g1] at h5
      simp [g2] at h6
      -- Therefore the fourth powers must be zero, which means √a=√c and √b=√d
      replace h5 : √a = √c:= by linarith
      replace h6 : √b = √d:= by linarith
      -- Converting back to the original variables
      rw [show a = √a ^ 2 by field_simp]
      rw [show b = √b ^ 2 by field_simp]
      rw [show c = √c ^ 2 by field_simp]
      rw [show d = √d ^ 2 by field_simp]
      rw [h5, h6]
      simp

    -- Backward direction: a=c and b=d implies equality
    .
      rintro ⟨rfl, rfl⟩
      field_simp
      linarith
