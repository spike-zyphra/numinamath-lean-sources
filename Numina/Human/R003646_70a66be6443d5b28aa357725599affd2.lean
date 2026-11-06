import Mathlib

open Real Finset

/- 11. (20 points) Given a positive real number $x$, define the sequence $\left\{a_{n}\right\}$ as $a_{n}=\frac{\mathrm{e}^{2 n x}-1}{\mathrm{e}^{2 n x}+1}$. Prove: For any positive integer $n$, we have
$$
a_{1} a_{2} \cdots a_{n}>1-\frac{2}{\mathrm{e}^{2 x}} .
$$
 -/
theorem inequalities_203593 {x : ℝ} (hx : 0 < x) (a : ℕ → ℝ)
    (ha : ∀ n, a n = (exp (2 * n * x) - 1) / (exp (2 * n * x) + 1)) :
    ∀ n, ∏ i ∈ range n, a (i + 1) > 1 - 2 / exp (2 * x) := by
  -- Let b = exp(2 * x).
  set b := exp (2 * x)
  -- We have 1 < b.
  have hb1 : 1 < b := by
    rw [one_lt_exp_iff]
    positivity
  -- We have 1 < b^(n + 1) for any natural n.
  have hbn n : 1 < b^(n + 1) := by
    apply one_lt_pow₀ hb1 (by linarith)
  -- We have a(n) = (b^n - 1) / (b^n + 1).
  replace ha n : a n = (b^n - 1) / (b^n + 1) := by
    simp [ha, b, ← Real.exp_nat_mul]
    ac_nf
  -- Show that 0 < a(n + 1).
  have ha0 n : 0 < a (n + 1) := by
    field_simp [ha]
    -- The result follows from 1 < b^(n + 1).
    exact hbn n
  intro n
  -- Consider two cases: b ≤ 2 and 2 < b.
  by_cases hb2 : b ≤ 2
  · -- If b ≤ 2 then show that 1 - 2 / b ≤ 0 and 0 < ∏ i ∈ range n, a(i + 1).
    apply lt_of_le_of_lt (b := 0)
    · field_simp
      apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    · apply prod_pos
      intro i hi
      exact ha0 i
  simp at hb2
  -- Assume that 2 < b.
  -- It is enough to show that ∏ i ∈ range n, a (i + 1) ≥ (1 - 2 / b) + 2 / (b * (b^n + 1))
  -- (because 2 / (b * (b^n + 1)) > 0).
  suffices h : ∏ i ∈ range n, a (i + 1) ≥ (1 - 2 / b) + 2 / (b * (b^n + 1)) by
    apply lt_of_lt_of_le _ h
    nth_rw 1 [← add_zero (1 - 2 / b)]
    gcongr
    positivity
  -- Proof by induction.
  induction n with
  | zero =>
    -- If n = 0 then the product is equal to 1 and 1 ≥ 1 - 2 / b + 2 / (2 * b).
    simp [← sub_nonneg]
    ring_nf
    positivity
  | succ n ih =>
    -- Assume that ∏ i ∈ range n, a (i + 1) ≥ (1 - 2 / b) + 2 / (b * (b^n + 1)) and
    -- show that ∏ i ∈ range (n + 1), a (i + 1) ≥ (1 - 2 / b) + 2 / (b * (b^(n + 1) + 1)).
    rw [prod_range_succ]
    -- Consider two cases: n = 0 and n ≠ 0.
    by_cases hn0 : n = 0
    · simp [hn0, ha]
      -- If n = 0 then we need to show that 1 - 2 / b + 2 / (b * (b + 1)) ≤ (b - 1) / (b + 1).
      field_simp
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      ring_nf
      exact le_refl _
    -- Assume that n ≠ 0.
    calc
      -- We have
      -- ∏ i ∈ range (n + 1), a (i + 1) = ∏ i ∈ range n, a (i + 1) * a(n + 1)
      --     ≥ (1 - 2 / b + 2 / (b * (b^n + 1))) * a (n + 1)
      --     = 1 - 2 / b + 2 * (2 * b^n + 1 - b) / (b * (b^n + 1) * (b^(n + 1) + 1))
      --     ≥ 1 - 2 / b + 2 * (b^n + 1) / (b * (b^n + 1) * (b^(n + 1) + 1))
      -- (because 2 * b^n + 1 - b ≥ b^n + 1 ↔ b^n ≥ b ↔ True)
      --     = (1 - 2 / b) + 2 / (b * b^(n + 1) + 1).
      _ ≥ (1 - 2 / b + 2 / (b * (b^n + 1))) * a (n + 1) := by
        gcongr
        exact le_of_lt (ha0 n)
      _ = 1 - 2 / b + 2 * (2 * b^n + 1 - b) / (b * (b^n + 1) * (b^(n + 1) + 1)) := by
        field_simp [ha]
        ring
      _ ≥ 1 - 2 / b + 2 * (b^n + 1) / (b * (b^n + 1) * (b^(n + 1) + 1)) := by
        gcongr
        suffices b^1 ≤ b^n by linarith
        apply pow_le_pow_right₀ (by linarith) (by omega)
      _ = (1 - 2 / b) + 2 / (b * (b^(n + 1) + 1)) := by
        field_simp
        ring