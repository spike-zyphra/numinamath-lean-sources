import Mathlib
/- 2. Determine $\mathrm{n} \in \mathrm{N}^{*}-\{1\}$ such that the number $a=\frac{1}{1+\sqrt{2}}+\frac{1}{\sqrt{2}+\sqrt{3}}+\ldots+\frac{1}{\sqrt{n-1}+\sqrt{n}}$ is an element of the set $A=\{x \in R /|x|<\sqrt{11-6 \sqrt{2}}\}$. -/
theorem algebra_112821 (a : ℕ → ℝ) (ha : a = fun n => ∑ i in Finset.range (n - 1), 1 / (√(i + 1) + √(i + 2))) : {n : ℕ | n > 1 ∧ |a n| < √(11 - 6 * √2)} = {2, 3, 4, 5, 6}:= by
  ext n
  -- Prove that 3 - √2 ≥ 0 (needed for later calculations)
  have h3 : 3 - √2 ≥ 0:= by
    -- Show that √2 ≤ 2, which implies 3 - √2 ≥ 1 > 0
    have h3 : (2 : ℝ) ≤ 2 ^ 2:= by linarith
    replace h3 : √2 ≤ √(2 ^ 2):= by exact Real.sqrt_le_sqrt h3
    field_simp at h3
    linarith
  -- Prove that a(n+1) ≥ 0 for all n (the sum is always non-negative)
  have hpos : ∀ n : ℕ, a (n + 1) ≥ 0:= by
    intro n
    induction n with
    | zero =>
      simp [ha]
    | succ n ih =>
      simp [ha] at ih ⊢
      rw [Finset.sum_range_succ]
      -- Each term in the sum is positive
      have g1 : (√(↑n + 1) + √(↑n + 2))⁻¹ ≥ 0:= by positivity
      linarith
  -- Key identity: a(n+1) = √(n+1) - 1 (telescoping sum formula)
  have h4 : ∀ n : ℕ, a (n + 1) = √(n + 1) - 1:= by
    intro n
    induction n with
    | zero =>
      simp [ha]
    | succ n ih =>
      simp [ha] at ih ⊢
      rw [Finset.sum_range_succ, ih]
      -- Algebraic manipulation to show telescoping property
      field_simp
      ring_nf
      field_simp
      ring_nf
  constructor
  -- Forward direction: if n ∈ {2,3,4,5,6}, then n > 1 and |a(n)| < √(11-6√2)
  .
    intro h
    simp at h
    rcases h with ⟨h1, h2⟩
    -- Rewrite 11 - 6√2 as (3 - √2)²
    rw [show 11 - 6 * √2 = (3 - √2) ^ 2 by ring_nf ; field_simp ; linarith] at h2
    specialize h4 (n - 1)
    have h5 : n - 1 + 1 = n:= by omega
    specialize hpos (n - 1)
    rw [h5] at h4 hpos
    -- Use the fact that a(n) ≥ 0 to remove absolute value
    rw [abs_of_nonneg hpos] at h2
    rify at h5
    replace h5 : (↑(n - 1) : ℝ) = (↑n : ℝ) - 1:= by linarith
    rw [h5] at h4
    ring_nf at h4
    field_simp at h2
    -- From |a(n)| < 3 - √2, we get √n - 1 < 3 - √2, so √n < 4 - √2
    replace h4 : √n < 4 - √2:= by linarith
    replace h3 : 4 - √2 ≥ 0:= by linarith
    rw [show √n = |√n| by exact Eq.symm (abs_of_nonneg (by positivity))] at h4
    rw [Eq.symm (abs_of_nonneg h3)] at h4
    -- Square both sides to get n < (4 - √2)²
    replace h4 : √n ^ 2 < (4 - √2) ^ 2:= by exact sq_lt_sq.mpr h4
    field_simp at h4
    ring_nf at h4
    field_simp at h4
    ring_nf at h4
    -- Show that 18 - 8√2 ≤ 7 using √2 ≥ 11/8
    replace h5 : 18 - √2 * 8 ≤ 7:= by
      suffices √2 ≥ 11 / 8 by linarith
      have g1 : (2 : ℝ) ≥ (11 / 8) ^ 2:= by linarith
      replace g1 : √2 ≥ √((11 / 8) ^ 2):= by exact Real.sqrt_le_sqrt g1
      field_simp at g1
      linarith
    -- Therefore n < 7, which gives us n ∈ {2,3,4,5,6}
    replace h4 : n < 7:= by
      rify
      linarith
    simp
    omega
  -- Backward direction: if n > 1 and |a(n)| < √(11-6√2), then n ∈ {2,3,4,5,6}
  .
    intro h
    -- Rewrite the inequality using (3 - √2)²
    rw [show 11 - 6 * √2 = (3 - √2) ^ 2 by ring_nf ; field_simp ; linarith]
    field_simp
    simp at h
    refine ⟨by omega, ?_⟩
    specialize h4 (n - 1)
    specialize hpos (n - 1)
    rw [show n - 1 + 1 = n by omega] at h4 hpos
    -- Use non-negativity to remove absolute value
    rw [abs_of_nonneg hpos]
    rw [h4]
    have h5 : n - 1 + 1 = n:= by omega
    rify at h5
    replace h5 : (↑(n - 1) : ℝ) = (↑n : ℝ) - 1:= by linarith
    rw [h5]
    simp
    replace h3 : 4 - √2 ≥ 0:= by linarith
    -- Need to show √n - 1 < 3 - √2, i.e., √n < 4 - √2
    suffices √n < 4 - √2 by linarith
    rw [show √n = |√n| by exact Eq.symm (abs_of_nonneg (by positivity))]
    rw [Eq.symm (abs_of_nonneg h3)]
    -- Square both sides
    suffices √n ^ 2 < (4 - √2) ^ 2 by exact sq_lt_sq.mp this
    field_simp
    ring_nf
    field_simp
    ring_nf
    -- From the constraint, we have n ≤ 6
    replace h : n ≤ 6:= by omega
    rify at h
    -- Show that 6 < 18 - 8√2 using √2 < 3/2
    suffices 6 < 18 - √2 * 8 by linarith
    suffices √2 < 3 / 2 by linarith
    -- Use the approximation √2 ≤ 1.49
    have g1 : (2 : ℝ) ≤ (149 / 100) ^ 2:= by linarith
    replace g1 : √2 ≤ √((149 / 100) ^ 2):= by exact Real.sqrt_le_sqrt g1
    field_simp at g1
    linarith
