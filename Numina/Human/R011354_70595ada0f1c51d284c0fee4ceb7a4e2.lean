import Mathlib

/-
6. let $a, b, c$ be positive real numbers with $a+b+c \geq a b c$. Prove that at least two of the following three inequalities are correct:

$$
\frac{2}{a}+\frac{3}{b}+\frac{6}{c} \geq 6, \quad \frac{2}{b}+\frac{3}{c}+\frac{6}{a} \geq 6, \quad \frac{2}{c}+\frac{3}{a}+\frac{6}{b} \geq 6
$$
 -/
theorem inequalities_262331 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c ≥ a * b * c) :
    (2 / a + 3 / b + 6 / c ≥ 6 ∧ 2 / b + 3 / c + 6 / a ≥ 6) ∨
    (2 / a + 3 / b + 6 / c ≥ 6 ∧ 2 / c + 3 / a + 6 / b ≥ 6) ∨
    (2 / b + 3 / c + 6 / a ≥ 6 ∧ 2 / c + 3 / a + 6 / b ≥ 6) := by
  /-
  ## 1st solution

  Set $x=\frac{1}{a}, y=\frac{1}{b}$ and $z=\frac{1}{c}$. The constraint is then $x y+y z+z x \geq 1$ and the three inequalities become

  $$ \begin{aligned} & 2 x+3 y+6 z \geq 6 \\ & 2 y+3 z+6 x \geq 6 \\ & 2 z+3 x+6 y \geq 6 \end{aligned} $$
  -/
  let x := 1 / a
  let y := 1 / b
  let z := 1 / c
  have sum_prod_ge_1 : x * y + y * z + z * x ≥ 1 := by
    --nlinarith
    have : x * y + y * z + z * x = (a + b + c) / (a * b * c) := by
      unfold x y z
      field_simp
      ring
    rw [this]
    have : a * b * c > 0 := by
      positivity
    exact (one_le_div₀ this).mpr h
  let u := 2 * x + 3 * y + 6 * z
  let v := 2 * y + 3 * z + 6 * x
  let w := 2 * z + 3 * x + 6 * y
  suffices u ≥ 6 ∧ v ≥ 6 ∨ u ≥ 6 ∧ w ≥ 6 ∨ v ≥ 6 ∧ w ≥ 6 by
    convert this using 3 <;>
    ring_nf
  -- It is now sufficient to show that the sum of two of the three terms on the left-hand side of this system is at least equal to 12, because then surely two of the three inequalities cannot be false at the same time.
  suffices u + v ≥ 12 ∧ v + w ≥ 12 ∧ w + u ≥ 12 by
    --tauto
    by_contra not_two_term_ge_6
    --simp at not_two_term_ge_6
    have two_term_lt_6 : (¬u ≥ 6 ∧ ¬v ≥ 6) ∨ (¬v ≥ 6 ∧ ¬w ≥ 6) ∨ (¬w ≥ 6 ∧ ¬u ≥ 6) := by
      tauto
    simp at two_term_lt_6
    rcases two_term_lt_6 with _ | _ | _ <;>
    . linarith
  have x_pos : 0 < x := by positivity
  have y_pos : 0 < y := by positivity
  have z_pos : 0 < z := by positivity
  -- Because of the cyclic symmetry, this proof is sufficient for the sum of the first two terms.
  suffices ∀ x : ℝ, x > 0 → ∀ y : ℝ, y > 0 → ∀ z : ℝ, z > 0 →
      x * y + y * z + z * x ≥ 1 →
      (2 * x + 3 * y + 6 * z) + (2 * y + 3 * z + 6 * x) ≥ 12 by
    unfold u v w
    exact ⟨
      this x x_pos y y_pos z z_pos sum_prod_ge_1,
      this y y_pos z z_pos x x_pos (by linarith),
      this z z_pos x x_pos y y_pos (by linarith)
    ⟩
  intro x x_pos y y_pos z z_pos sum_prod_ge_1
  /-
  After squaring, we must therefore show that

  $$ (2 x+3 y+6 z+2 y+3 z+6 x)^{2} \geq 144 $$
  -/
  suffices ((2 * x + 3 * y + 6 * z) + (2 * y + 3 * z + 6 * x)) ^ 2 ≥ 144 by
    nlinarith
  /-
  Because of the constraint, it is sufficient to show that the left-hand side is at least equal to $144(x y+y z+z x)$. Multiplying out and simplifying now gives the inequality

  $$ 64 x^{2}+25 y^{2}+81 z^{2}-64 x y-54 y z \geq 0 $$
  -/
  /-
  suffices ((2 * x + 3 * y + 6 * z) + (2 * y + 3 * z + 6 * x)) ^ 2 ≥ 144 * (x * y + y * z + z * x) by
    linarith
   -/
  /-
  However, the left-hand side is a sum of two squares and so everything is shown:

  $$ (8 x-4 y)^{2}+(3 y-9 z)^{2} \geq 0 $$
  -/
  have : (8 * x - 4 * y) ^ 2 + (3 * y - 9 * z) ^ 2 ≥ 0 := by
    nlinarith
  linarith
