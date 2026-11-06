import Mathlib

open Real

/- 14. Find the smallest number $k$ such that for all real numbers $x, y$ and $z$

$$

\left(x^{2}+y^{2}+z^{2}\right)^{2} \leq k\left(x^{4}+y^{4}+z^{4}\right) \text {. }

$$
 -/
theorem inequalities_218291 (k : ℝ) :
    (∀ x y z : ℝ, (x^2 + y^2 + z^2)^2 ≤ k * (x^4 + y^4 + z^4)) ↔ k ≥ 3 := by
  constructor
  · -- We prove that k is at least 3 by providing a counter example when k is less than 2
    rintro h
    -- Use the contrapositive
    contrapose! h
    -- We simply use the counter example (1, 1, 1)
    use 1
    use 1
    use 1
    norm_num
    linarith
  intro hk x y z
  -- Define our vectors to use Cauchy Schwarz on
  let u : Fin 3 → ℝ := ![x^2, y^2, z^2]
  let v : Fin 3 → ℝ := ![1, 1, 1]
  -- Cauchy Schwarz inequality
  have : _ := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  calc
    (x^2 + y^2 + z^2)^2 ≤ 3 * (x^4 + y^4 + z^4) := by
      unfold u v at this
      simp [Fin.sum_univ_three] at this
      linarith
    _ ≤ k * (x^4 + y^4 + z^4) := by
      apply mul_le_mul_of_nonneg
      · tauto
      · tauto
      · positivity
      positivity