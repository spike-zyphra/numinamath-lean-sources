import Mathlib

/- Let $x, y, z, p, q, r$ be positive real numbers such that $p + q + r = 1$ and $x^p y^q z^r = 1$. Prove that
\[
\frac{p^2 x^2}{q y + r z} + \frac{q^2 y^2}{p x + r z} + \frac{r^2 z^2}{p x + q y} \geq \frac{1}{2}.
\] -/
theorem inequalities_617513 (x y z p q r : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hsum : p + q + r = 1) (hprod : x ^ p * y ^ q * z ^ r = 1) :
    1 / 2 ≤ p ^ 2 * x ^ 2 / (q * y + r * z) + q ^ 2 * y ^ 2 / (p * x + r * z) + r ^ 2 * z ^ 2 / (p * x + q * y) := by

  -- 1. By the Cauchy-Schwarz inequality in Engel form,
  -- we have: [ \frac{p^2 x^2}{q y + r z} + \frac{q^2 y^2}{p x + r z} + \frac{r^2 z^2}{p x + q y} \geq \frac{(p x + q y + r z)^2}{2(p x + q y + r z)} ]
  let f (i : Fin 3) :=
    match i with
    | 0 => p * x
    | 1 => q * y
    | 2 => r * z
  let g (i : Fin 3) :=
    match i with
    | 0 => q * y + r * z
    | 1 => p * x + r * z
    | 2 => p * x + q * y
  have hg : ∀ x ∈ Finset.univ, g x > 0 := by
    intro x _
    simp [g]
    fin_cases x
    all_goals
      simp
      positivity
  obtain h := Finset.sq_sum_div_le_sum_sq_div _ f hg
  simp [f, g, Fin.sum_univ_succ, mul_pow] at h
  rw [add_assoc]
  apply le_trans ?_ h
  -- 1. Simplifying the right-hand side, we get: [ \frac{(p x + q y + r z)^2}{2(p x + q y + r z)} = \frac{p x + q y + r z}{2} ]
  trans (p * x + q * y + r * z) / 2
  · --1. Therefore, it suffices to prove that: [ p x + q y + r z \geq 1 ]
    -- which is obvious by the GM-AM inequality
    apply div_le_div_of_nonneg_right
    · apply le_trans ?_ (Real.geom_mean_le_arith_mean3_weighted (le_of_lt hp) (le_of_lt hq) (le_of_lt hr) (le_of_lt hx) (le_of_lt hy) (le_of_lt hz) hsum)
      rw [hprod]
    · simp
  · apply le_of_eq
    field_simp
    ring
