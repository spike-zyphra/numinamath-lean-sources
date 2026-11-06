import Mathlib

/- Let $ a, b, c $ be three strictly positive real numbers. Show that
$$
\frac{a^{4}+1}{b^{3}+b^{2}+b}+\frac{b^{4}+1}{c^{3}+c^{2}+c}+\frac{c^{4}+1}{a^{3}+a^{2}+a} \geqslant 2
$$ -/
theorem inequalities_605800
    (a b c d : ℝ)
    (ha : 0 ≤ a)
    (hb : a ≤ b)
    (hc : b ≤ c)
    (hd : c ≤ d) :
    a^2 * b^2 + b^2 * c^2 + c^2 * d^2 + d^2 * a^2 ≤ a * b^3 + b * c^3 + c * d^3 + d * a^3 := by

  -- lemma, for positive real number, $a ^ 2 \le b ^ 2 \rarr a \le b$
  have l_le_of_sq_le_sq_of_rpos {a b : ℝ} (hb : 0 ≤ b) : a ^ 2 ≤ b ^ 2 → a ≤ b := by
    intro h
    apply sq_le_sq.mp at h
    trans |a|
    . exact le_abs_self a
    rw [abs_of_nonneg hb] at h
    exact h

  -- The inequality is equivalent to $$ \left(a b^{3}+b c^{3}+c d^{3}+d a^{3}\right)^{2} \geq\left(a^{2} b^{2}+b^{2} c^{2}+c^{2} d^{2}+d^{2} a^{2}\right)^{2} $$
  have r0 : 0 ≤ a * b ^ 3 + b * c ^ 3 + c * d ^ 3 + d * a ^ 3 := by
    rw [add_assoc]
    apply add_nonneg
    <;> apply add_nonneg
    <;> exact mul_nonneg (by linarith) (pow_nonneg (by linarith) _)
  apply l_le_of_sq_le_sq_of_rpos r0


  -- By the Cauchy-Schwarz inequality, $$ \left(a b^{3}+b c^{3}+c d^{3}+d a^{3}\right)\left(a^{3} b+b^{3} c+c^{3} d+d^{3} a\right) \geq\left(a^{2} b^{2}+b^{2} c^{2}+c^{2} d^{2}+d^{2} a^{2}\right)^{2} $$
  have r1 : (a^2 * b^2 + b^2 * c^2 + c^2 * d^2 + d^2 * a^2) ^ 2 ≤ (a * b^3 + b * c^3 + c * d^3 + d * a^3) * (a^3 * b + b^3 * c + c^3 * d + d^3 * a) := by
    let f : Fin 4 → ℝ := ![√(a*b^3), √(b*c^3), √(c*d^3), √(d*a^3)]
    let g : Fin 4 → ℝ := ![√(a^3*b), √(b^3*c), √(c^3*d), √(d^3*a)]
    convert Finset.sum_mul_sq_le_sq_mul_sq {0, 1, 2, 3} f g using 1
    -- left side is equal
    . simp [← add_assoc]
      have : f 0 * g 0 = a ^ 2 * b ^ 2 ∧
              f 1 * g 1 = b ^ 2 * c ^ 2 ∧
              f 2 * g 2 = c ^ 2 * d ^ 2 ∧
              f 3 * g 3 = d ^ 2 * a ^ 2 := by
        repeat any_goals constructor
        any_goals
          simp only [show f 0 = √(a*b^3) ∧ f 1 = √(b*c^3) ∧ f 2 = √(c*d^3) ∧ f 3 = √(d*a^3) from ⟨rfl, rfl, rfl, rfl⟩,
                      show g 0 = √(a^3*b) ∧ g 1 = √(b^3*c) ∧ g 2 = √(c^3*d) ∧ g 3 = √(d^3*a) from ⟨rfl, rfl, rfl, rfl⟩]
          rw [← Real.sqrt_mul (show 0 ≤ _ * _ ^ 3 by apply mul_nonneg (by linarith) (pow_nonneg (by linarith) 3))]
          exact (Real.sqrt_eq_iff_eq_sq (by ring_nf; positivity) (by positivity)).mpr (by ring)
      simp only [this]
    -- right side is equal
    . congr 1
      all_goals
        simp [← add_assoc]
        simp only [show f 0 = √(a*b^3) ∧ f 1 = √(b*c^3) ∧ f 2 = √(c*d^3) ∧ f 3 = √(d*a^3) from ⟨rfl, rfl, rfl, rfl⟩,
                    show g 0 = √(a^3*b) ∧ g 1 = √(b^3*c) ∧ g 2 = √(c^3*d) ∧ g 3 = √(d^3*a) from ⟨rfl, rfl, rfl, rfl⟩]
        repeat rw [Real.sq_sqrt]
        all_goals apply mul_nonneg
      any_goals linarith
      any_goals exact pow_nonneg (by linarith) 3

  -- Hence it is sufficient to prove that $$ \left(a b^{3}+b c^{3}+c d^{3}+d a^{3}\right)^{2} \geq\left(a b^{3}+b c^{3}+c d^{3}+d a^{3}\right)\left(a^{3} b+b^{3} c+c^{3} d+d^{3} a\right) $$
  suffices : (a * b^3 + b * c^3 + c * d^3 + d * a^3) * (a^3 * b + b^3 * c + c^3 * d + d^3 * a) ≤ (a * b ^ 3 + b * c ^ 3 + c * d ^ 3 + d * a ^ 3) ^ 2
  . linarith only [r1, this]

  -- i.e. to prove $a b^{3}+b c^{3}+c d^{3}+d a^{3} \geq a^{3} b+b^{3} c+c^{3} d+d^{3} a$.
  suffices : (a^3 * b + b^3 * c + c^3 * d + d^3 * a) ≤ (a * b ^ 3 + b * c ^ 3 + c * d ^ 3 + d * a ^ 3)
  . simp only [pow_two, mul_le_mul_of_nonneg_left this r0]

  -- This inequality can be written successively which comes down to $$ (a-c)(b-d)\left(b^{2}+b d+d^{2}-a^{2}-a c-c^{2}\right) \geq 0 $$
  suffices : 0 ≤ (a - c) * (b - d) * (b^2 + b * d + d^2 - a^2 - a * c - c^2)
  . linarith

  -- The last inequality is true because $a-c \leq 0$, $b-d \leq 0$, and $\left(b^{2}-a^{2}\right)+(b d-a c)+\left(d^{2}-c^{2}\right) \geq 0$ as a sum of three non-negative numbers.
  apply mul_nonneg
  . exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  . nlinarith
