import Mathlib

open Real Set
open scoped BigOperators

/- Let the maximum and minimum elements of the set $ \left{ \frac{5}{x}+y|1\leqslant x\leqslant y \leqslant5\right}$ be $M$ and $N$, respectively, then $MN=$ ___          ___. -/
theorem algebra_8647 {M N : ℝ}
  (hM : ∃ x y, x ∈ Icc 1 5 ∧ y ∈ Icc 1 5 ∧ x ≤ y ∧ 5 / x + y = M)
  (hN : ∃ x y, x ∈ Icc 1 5 ∧ y ∈ Icc 1 5 ∧ x ≤ y ∧ 5 / x + y = N)
  (hMub : ∀ x y, x ∈ Icc 1 5 ∧ y ∈ Icc 1 5 ∧ x ≤ y → 5 / x + y ≤ M)
  (hNlb : ∀ x y, x ∈ Icc 1 5 ∧ y ∈ Icc 1 5 ∧ x ≤ y → 5 / x + y ≥ N) :
  M * N = 20 * sqrt 5 := by

  -- First prove M = 10, so maximum value is M.
  have h1 := hMub 1 5 (by
    constructor
    · -- Show 1 ∈ Icc 1 5
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show 5 ∈ Icc 1 5
      exact ⟨by norm_num, by norm_num⟩
    · -- Show 1 ≤ 5
      norm_num
    )
  have hMge : M ≥ 10 := by
    norm_num at h1 ⊢
    linarith

  -- Show M ≤ 10
  have hMle : M ≤ 10 := by
    rcases hM with ⟨x, y, hx, hy, hxy, heq⟩
    rw [mem_Icc] at hx hy
    have hx1 : 1 ≤ x := hx.1
    have hx5 : x ≤ 5 := hx.2
    have hy1 : 1 ≤ y := hy.1
    have hy5 : y ≤ 5 := hy.2
    have h2 : 5 / x ≤ (5 : ℝ) := by
      apply (div_le_iff₀ (by linarith)).mpr
      nlinarith
    nlinarith

  have hM_eq : M = 10 := by linarith [hMge, hMle]

  -- Second prove N = 2*sqrt(5).
  have h2 := hNlb (Real.sqrt 5) (Real.sqrt 5) (by
    constructor
    · -- Show √5 ∈ Icc 1 5
      constructor
      · -- Show 1 ≤ √5
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 1]
      · -- Show √5 ≤ 5
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    constructor
    · -- Show √5 ∈ Icc 1 5
      constructor
      · -- Show 1 ≤ √5
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 1]
      · -- Show √5 ≤ 5
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    · -- Show √5 ≤ √5
      linarith
    )
  have hNle : N ≤ 2 * Real.sqrt 5 := by
    have h5divsqrt5 : 5 / (Real.sqrt 5) = Real.sqrt 5 := by
      field_simp [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num)]
      <;> nlinarith [Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    nlinarith [h5divsqrt5, Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num)]

  -- Show N ≥ 2*sqrt(5)
  have hNge : N ≥ 2 * Real.sqrt 5 := by
    rcases hN with ⟨x, y, hx, hy, hxy, heq⟩
    rw [mem_Icc] at hx hy
    have hx1 : 1 ≤ x := hx.1
    have hx5 : x ≤ 5 := hx.2
    have hy1 : 1 ≤ y := hy.1
    have hy5 : y ≤ 5 := hy.2
    have h3 : 5 / x + y ≥ 2 * Real.sqrt 5 := by
      have h4 : 5 / x + y ≥ 5 / x + x := by
        have h5 : (5 / x + y) - (5 / x + x) ≥ 0 := by
          have : y ≥ x := hxy
          nlinarith
        linarith
      have h5 : 5 / x + x ≥ 2 * Real.sqrt 5 := by
        have h6 : x > 0 := by linarith
        have h7 : 5 / x + x - 2 * Real.sqrt 5 ≥ 0 := by
          have h8 : (5 / x + x - 2 * Real.sqrt 5) = (5 + x^2 - 2 * x * Real.sqrt 5) / x := by
            field_simp
            ring
          rw [h8] at *
          have h9 : 5 + x ^ 2 - 2 * x * Real.sqrt 5 = (x - Real.sqrt 5) ^ 2 := by
            nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
          have h10 : (5 + x ^ 2 - 2 * x * Real.sqrt 5 : ℝ) ≥ 0 := by
            rw [h9]
            have h11 : (x - Real.sqrt 5) ^ 2 ≥ 0 := by
              exact sq_nonneg (x - Real.sqrt 5)
            linarith
          apply div_nonneg h10 (by linarith)
        linarith
      linarith
    linarith

  have hN_eq : N = 2 * Real.sqrt 5 := by linarith [hNle, hNge]

  rw [hM_eq, hN_eq]
  nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]