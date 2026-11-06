import Mathlib

open Set Real

/-
Solve the inequality
$\frac{\sqrt{\frac{x}{\gamma}+(\alpha+2)}-\frac{x}{\gamma}-\alpha}{x^{2}+a x+b} \geqslant 0$.

In your answer, specify the number equal to the number of integer roots of this inequality.
If there are no integer roots, or if there are infinitely many roots,
enter the digit 0 in the answer sheet.

$$ \alpha=3, \gamma=1, a=-15, b=54 . $$
-/

theorem inequalities_185544 :
    let α := 3
    let γ := 1
    let a := -15
    let b := 54
-- The inequation of interest
    let ineq (x : ℝ) := (√(x / γ + (α + 2)) - x / γ - α) / (x ^ 2 + a * x + b) ≥ 0
-- The domain is $[-5, \infty)$ excluding $6$ and $9$.
    let S := { x ∈ Ici (-5 : ℤ) \ {6, 9} | ineq x }
    S.ncard = 7
    := by
  intro α γ a b ineq S

-- Given the inequality and the values $\alpha = 3$, $\gamma = 1$, $a = -15$, and $b = 54$,
-- we substitute these values into the inequality:
-- $$ \frac{\sqrt{x + 5} - x - 3}{(x - 6)(x - 9)} \geq 0 $$
  have h1 x : ineq x ↔ (√(x + 5) - x - 3) / ((x - 6) * (x - 9)) ≥ 0 := by
    dsimp [ineq, α, γ, a, b]
    ring_nf

-- Next, we show that the numerator $\sqrt{x + 5} - x - 3 \ge 0$ iff $x \le -1$.
  have h2 x (hx : x ≥ -5) : √(x + 5) - x - 3 ≥ 0 ↔ x ≤ -1 := calc
      _ ↔ √(x + 5) ≥ x + 3 := by constructor <;> intro c1 <;> linarith
      _ ↔ _ := by
        obtain hx2 | hx2 : x ≥ -3 ∨ x ≤ -3 := by apply le_total
        . calc
          _ ↔ √(x + 5) ^ 2 ≥ (x + 3) ^ 2 := by
            have c1 : √(x + 5) ≥ 0 := by apply sqrt_nonneg
            have c2 : (x + 3) ≥ 0 := by linarith
            exact (sq_le_sq₀ c2 c1).symm
          _ ↔ x + 5 ≥ x ^ 2 + 6 * x + 9 := by
            have c1 : x + 5 ≥ 0 := by linarith
            simp [sq_sqrt c1]
            ring_nf
          _ ↔ x ^ 2 + 5 * x + 4 ≤ 0 := by constructor <;> intro c1 <;> linarith
          _ ↔ (x + 1) * (x + 4) ≤ 0 := by ring_nf
          _ ↔ _ := by constructor <;> intro c1 <;> nlinarith
        . constructor <;> intro c1
          . linarith
          . have c2 : √(x + 5) ≥ 0 := by apply sqrt_nonneg
            linarith
  have h2' x (hx : x ≥ -5) : √(x + 5) - x - 3 ≤ 0 ↔ x ≥ -1 := calc
      _ ↔ √(x + 5) ≤ x + 3 := by constructor <;> intro c1 <;> linarith
      _ ↔ _ := by
        obtain hx2 | hx2 : x ≥ -3 ∨ x < -3 := by apply le_or_lt
        . calc
          _ ↔ √(x + 5) ^ 2 ≤ (x + 3) ^ 2 := by
            have c1 : √(x + 5) ≥ 0 := by apply sqrt_nonneg
            have c2 : (x + 3) ≥ 0 := by linarith
            exact (sq_le_sq₀ c1 c2).symm
          _ ↔ x + 5 ≤ x ^ 2 + 6 * x + 9 := by
            have c1 : x + 5 ≥ 0 := by linarith
            simp [sq_sqrt c1]
            ring_nf
          _ ↔ x ^ 2 + 5 * x + 4 ≥ 0 := by constructor <;> intro c1 <;> linarith
          _ ↔ (x + 1) * (x + 4) ≥ 0 := by ring_nf
          _ ↔ _ := by constructor <;> intro c1 <;> nlinarith
        . constructor <;> intro c1
          . have c2 : √(x + 5) ≥ 0 := by apply sqrt_nonneg
            linarith
          . linarith

-- And, we show that the denominator $(x - 6)(x - 9)$ is ≥ 0 if and only if (x ≤ 6 or x ≥ 9)
  have h3 (x : ℝ) : (x - 6) * (x - 9) ≥ 0 ↔ (x ≤ 6 ∨ x ≥ 9) := by
    constructor
    . intro c1
      by_contra c2
      push_neg at c2
      nlinarith
    . intro c1
      obtain c1 | c1 := c1 <;> nlinarith
  have h3' (x : ℝ) : (x - 6) * (x - 9) ≤ 0 ↔ (x ≥ 6 ∧ x ≤ 9) := by
    rw [mul_nonpos_iff]
    constructor
    . intro c1
      obtain c1 | c1 := c1 <;> split_ands <;> linarith
    . intro c1
      left
      split_ands <;> linarith

-- Combining these, the inequality $\frac{\sqrt{x + 5} - x - 3}{(x - 6)(x - 9)} \geq 0$ holds when:
-- - Both numerator and denominator are non-negative or both are non-positive.
-- - The solution intervals are $[-5, -1] \cup (6, 9)$.
  have h4 (x : ℤ) (hx : x ∈ Ici (-5) \ {6, 9}) : ineq x
        ↔ (x ∈ Icc (-5) (-1) ∨ x ∈ Ioo 6 9) := by
    rw [h1]
    simp at hx
    specialize h2 x (by norm_cast; simp; omega)
    specialize h2' x (by norm_cast; simp; omega)
    specialize h3 x
    specialize h3' x
    simp only [div_nonneg_iff, h2, h3, h2', h3']
    norm_cast
    simp
    omega

-- The integer solutions within these intervals are:
-- - From $[-5, -1]$: $-5, -4, -3, -2, -1$ (5 integers).
-- - From $(6, 9)$: $7, 8$ (2 integers).
-- Thus, the number of integer roots is $5 + 2 = 7$.
  have h5 : S.ncard = 7 := by
    let T := {x | x ∈ Ici (-5) \ {6, 9} ∧ (x ∈ Icc (-5) (-1) ∨ x ∈ Ioo 6 9)}
    have c1 : S = T := by
      ext x
      by_cases hx : x ∈ Ici (-5) \ {6, 9}
      . simp at hx
        simp [S, T, hx, h4 x (by simp; norm_cast)]
      . simp at hx
        replace hx : ¬(-5 ≤ x ∧ ¬x = 6 ∧ ¬x = 9) := by omega
        simp [S, T, hx]

    let T1 := { x ∈ Finset.Icc (-5) (-1) | x ∈ Ici (-5) \ {6, 9} }
    let T2 := { x ∈ Finset.Icc 6 9 | x ∈ Ici (-5) \ {6, 9} }

    have c2 : T = T1 ∪ T2 := by ext x; simp [T, T1, T2]; omega
    have c3 : T1 = {-5, -4, -3, -2, -1} := by decide
    have c4 : T2 = {7, 8} := by decide

    rw [c1, c2]
    push_cast
    rw [c3, c4]
    rw [ncard_union_eq]
    . simp only [ncard_coe_Finset]
      decide
    . intro s hs1 hs2 x hx
      specialize hs1 hx
      specialize hs2 hx
      simp at hs1 hs2 ⊢
      omega

  exact h5
