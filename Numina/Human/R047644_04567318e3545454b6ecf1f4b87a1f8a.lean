import Mathlib


/--
  Determine the largest real number $c$ such that for any 2017 real numbers $x_{1}, x_{2}, \ldots, x_{2017}$, the inequality
  $$
  \sum_{i=1}^{2016} x_{i}\left(x_{i}+x_{i+1}\right) \geq c \cdot x_{2017}^{2}
  $$
  holds.
-/
theorem inequalities_609644 :
    IsGreatest {c : ℝ | ∀ x : ℕ → ℝ, ∑ i in Finset.range 2016, x i * (x i + x (i + 1)) ≥ c * x 2016 ^ 2} (-1008 / 2017) := by

  -- Define a sequence of real numbers $\left\{p_{k}\right\}$ by $p_k = k / (2k + 2)$.
  let p (k : ℕ) : ℝ := k / (2 * k + 2)

  -- One can show by induction that p_(k+1) = 1 / (4 * (1 - p_k)).
  have hp {k : ℕ} : p (k + 1) = 1 / (4 * (1 - p k)) := by
    simp only [p]
    field_simp
    have : 4 * (2 * ↑k + (2 : ℝ) - ↑k) ≠ (0 : ℝ) := by
      ring_nf
      norm_cast
      simp
    field_simp
    ring

  -- We can show that $p_{k+1} \neq 0$ and $p_{k+1} \geq 0$.
  have hpne {k : ℕ} : p (k + 1) ≠ 0 := by
    simp [p]
    norm_cast
  have hpge {k : ℕ} : p (k + 1) ≥ 0 := by
    simp [p]
    apply div_nonneg
    all_goals (norm_cast; simp)

  -- Note that, for every $i \geq 1$,
  -- $$ \left(1-p_{i}\right) \cdot x_{i}^{2}+x_{i} x_{i+1}+p_{i+1} x_{i+1}^{2}=\left(\frac{x_{i}}{2 \sqrt{p_{i+1}}}+\sqrt{p_{i+1}} x_{i+1}\right)^{2} \geq 0 $$
  have hxp {k : ℕ} {x : ℕ → ℝ} : (1 - p k) * (x k) ^ 2 + x k * x (k + 1) + p (k + 1) * x (k + 1) ^ 2 ≥ 0 := by
    calc
      _ = 1 / (4 * p (k + 1)) * (x k) ^ 2 + x k * x (k + 1) + p (k + 1) * x (k + 1) ^ 2 := by simp [hp]; left; ring
      _ = (x k / (2 * √(p (k + 1))) + √(p (k + 1)) * x (k + 1)) ^ 2 := by
        rw [add_sq, mul_pow, div_pow, mul_pow, Real.sq_sqrt hpge, div_mul_eq_div_div (x k), ←mul_assoc, ←mul_div_assoc 2]
        rw [div_mul_cancel₀]
        ring
        exact (Real.sqrt_ne_zero hpge).mpr hpne
      _ ≥ 0 := by exact sq_nonneg (x k / (2 * √(p (k + 1))) + √(p (k + 1)) * x (k + 1))

  -- i.e., x_k * (x_k + x_(k+1)) ≥ p_k * (x_k)^2 - p_(k+1) * (x_(k+1))^2.
  have hxp' {k : ℕ} {x : ℕ → ℝ} : x k * (x k + x (k + 1)) ≥ p k * (x k) ^ 2 - p (k + 1) * x (k + 1) ^ 2 := by
    calc
      _ = (1 - p k) * (x k) ^ 2 + x k * x (k + 1) + p (k + 1) * x (k + 1) ^ 2 + p k * (x k) ^ 2 - p (k + 1) * x (k + 1) ^ 2 := by ring
      _ ≥ 0 + p k * (x k) ^ 2 - p (k + 1) * x (k + 1) ^ 2 := by rel [hxp]
      _ = _ := by simp

  -- Summing from $i=0$ to $n-1$ gives
  -- $$ \sum_{i=0}^{n-1} x_{i}\left(x_{i}+x_{i+1}\right) \geq-p_{n} x_{n}^{2} $$
  have hsum {x : ℕ → ℝ} {k : ℕ} : ∑ i in Finset.range k, x i * (x i + x (i + 1)) ≥ - p k * x k ^ 2 := by
    induction k with
    | zero => simp [p]
    | succ k ih =>
      rw [Finset.sum_range_succ]
      calc
        _ ≥ -p k * x k ^ 2 + (p k * (x k) ^ 2 - p (k + 1) * x (k + 1) ^ 2) := by rel [ih, hxp']
        _ = _ := by ring

  simp [IsGreatest]
  constructor
  · -- show that the case -1008 / 2017 is in the set by showing p 2016 = -1008 / 2017.
    intro _
    apply le_trans ?_ hsum
    simp [p]
    norm_num
  · -- show that -1008 / 2017 is the largest by constructing a tight example.
    simp [upperBounds]
    intro _ hx
    -- x_k = (-1)^k * (k + 1)
    let x (k : ℕ) : ℝ := (-1) ^ k * (k + 1)
    -- then we have that ∑_{i=0}^{n-1} x_{i}\left(x_{i}+x_{i+1}\right) = - (n + 1) * n / 2
    have hxsum {k : ℕ} : ∑ i in Finset.range k, x i * (x i + x (i + 1)) = - (k + 1) * k / 2 := by
      induction k with
      | zero => simp
      | succ k' ih =>
        rw [Finset.sum_range_succ, ih]
        simp [x]
        ring_nf
        simp
        ring
    -- then  we have that - (k + 1) * k / 2 = - p k * x k ^ 2
    obtain hx := hx x
    rw [hxsum] at hx
    norm_num at hx
    -- therefore c ≤ -1008 / 2017
    linarith
