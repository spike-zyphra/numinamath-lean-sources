import Mathlib

open Finset Real

theorem inequalities_83783 (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (h : ∏ i, a i = 1) :
    ∏ i, (1 + a i) ≥ 2 ^ n := by
  have h1 : ∀ i, 1 + a i ≥ 2 * Real.sqrt (a i) := by
    intro i
    have h2 : 0 < a i := ha i
    have h3 : (Real.sqrt (a i)) ^ 2 = a i := Real.sq_sqrt (show 0 ≤ a i by linarith)
    nlinarith [sq_nonneg (Real.sqrt (a i) - 1), Real.sqrt_nonneg (a i),
      sq_nonneg (a i - 1)]
  -- Multiply up AM-GM over all i
  have h2 : ∏ i : Fin n, (1 + a i) ≥ ∏ i : Fin n, (2 * Real.sqrt (a i)) := by
    apply Finset.prod_le_prod
    · -- Show that for all i, 0 ≤ (2 * sqrt (a i) : ℝ)
      intro i _
      have h11 : 0 < a i := ha i
      have h12 : 0 < Real.sqrt (a i) := by
        apply Real.sqrt_pos.mpr
        linarith
      nlinarith [Real.sqrt_nonneg (a i)]
    · -- Show that for all i, (1 + a i) ≥ (2 * Real.sqrt (a i))
      intro i _
      exact h1 i
  -- Extract 2^n from product
  have h3 : ∏ i : Fin n, (2 * Real.sqrt (a i)) = (2 ^ n) * (∏ i : Fin n, Real.sqrt (a i)) := by
    calc
      ∏ i : Fin n, (2 * Real.sqrt (a i))
        = ∏ i : Fin n, (2 * (Real.sqrt (a i)) ) := by rfl
      _ = (∏ i : Fin n, (2 : ℝ)) * (∏ i : Fin n, (Real.sqrt (a i)) ) := by 
        rw [prod_mul_distrib]
      _ = (2 ^ n) * (∏ i : Fin n, (Real.sqrt (a i)) ) := by 
        simp [prod_const, Finset.card_univ]
  -- Show a key property that the product of sqrt(a i) is 1
  have h61 : (∏ i : Fin n, Real.sqrt (a i)) = 1 := by
    have h9 : (∏ i : Fin n, Real.sqrt (a i)) ^ 2 = (∏ i : Fin n, (a i : ℝ)) := by
      have h9 : ∀ i : Fin n, (Real.sqrt (a i)) ^ 2 = a i := by
        intro i
        have h6 : 0 ≤ a i := by
          have h7 : 0 < a i := ha i
          linarith
        rw [Real.sq_sqrt]
        linarith
      calc
        (∏ i : Fin n, Real.sqrt (a i)) ^ 2 = ∏ i : Fin n, ((Real.sqrt (a i)) ^ 2) := by
          rw [prod_pow]
        _ = ∏ i : Fin n, (a i : ℝ) := by
          apply Finset.prod_congr
          · rfl
          · intro x _
            specialize h9 x
            linarith
    -- Since ∏ i : Fin n, a i = 1 we get (∏ i : Fin n, Real.sqrt (a i)) = a value of Real.sqrt.
    rw [h] at h9
    have h87 : (∏ i : Fin n, Real.sqrt (a i)) ≥ 0 := by
      apply Finset.prod_nonneg
      intro i _
      have h10 : 0 < a i := ha i
      positivity
    have h110 : (∏ i : Fin n, Real.sqrt (a i)) ^ 2 = (1 : ℝ) := by
      linarith
    have h113 : (∏ i : Fin n, Real.sqrt (a i)) = Real.sqrt (1 : ℝ) := by
      have h93 : (∏ i : Fin n, Real.sqrt (a i)) ≥ 0 := h87
      have h97 : (∏ i : Fin n, Real.sqrt (a i)) ^ 2 = (1 : ℝ) := h110
      have h33 : Real.sqrt ((∏ i : Fin n, Real.sqrt (a i)) ^ 2) = Real.sqrt (1 : ℝ) := by
        rw [h97]
      have h94 : Real.sqrt ((∏ i : Fin n, Real.sqrt (a i)) ^ 2) =
          (∏ i : Fin n, Real.sqrt (a i)) := by
        rw [Real.sqrt_sq (show 0 ≤ (∏ i : Fin n, Real.sqrt (a i) : ℝ) by linarith)]
      nlinarith
    have h150 : Real.sqrt (1 : ℝ) = 1 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    nlinarith
  have h4 : ∏ i : Fin n, (2 * Real.sqrt (a i)) = 2 ^ n := by
    rw [h3, h61]
    all_goals
      norm_num
  -- Final conclusion
  linarith [h2, h4]