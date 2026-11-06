import Mathlib

open Real

theorem inequalities_222820 (n : ℕ) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (h : ∏ i, a i = 1) :
    ∏ i, (2 + a i) ≥ 3 ^ n := by

  have h1 : ∀ i, 0 < a i := ha

  have h3 : ∀ i, 2 + a i ≥ 3 * (a i) ^ (1 / 3 : ℝ) := by
    intro i
    have ha_pos : 0 < a i := ha i
    have h4 : (a i) ^ (1 / 3 : ℝ) ≥ 0 := by positivity
    have h5 : 2 + a i ≥ 3 * (a i) ^ (1 / 3 : ℝ) := by
      have h6 : ((a i) ^ (1 / 3 : ℝ)) ^ 3 = a i := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals linarith [ha_pos]
      nlinarith [sq_nonneg ((a i) ^ (1 / 3 : ℝ) - 1), sq_nonneg ((a i) ^ (1 / 3 : ℝ)), sq_nonneg (a i - 1),
        Real.rpow_nonneg (by linarith : 0 ≤ a i) (1 / 3 : ℝ)]
    linarith

  have h7 : ∏ i, (2 + a i) ≥ ∏ i, (3 * (a i) ^ (1 / 3 : ℝ)) := by
    apply Finset.prod_le_prod
    · -- Show that each term is non-negative
      intro i _
      have ha_pos : 0 < a i := ha i
      have h7 : 0 ≤ (a i) ^ (1 / 3 : ℝ) := by positivity
      nlinarith
    · -- Show that for each i, 2 + a i ≥ 3 * (a i) ^ (1 / 3 : ℝ)
      intro i _
      have h8 : 2 + a i ≥ 3 * (a i) ^ (1 / 3 : ℝ) := h3 i
      linarith

  have h8 : ∏ i, (3 * (a i) ^ (1 / 3 : ℝ)) = (3 ^ n : ℝ) * (∏ i, (a i) ^ (1 / 3 : ℝ)) := by
    calc
      ∏ i, (3 * (a i) ^ (1 / 3 : ℝ))
        = ∏ i, (3 * ((a i) ^ (1 / 3 : ℝ)) ) := by rfl
      _ = (∏ i, (3 : ℝ)) * (∏ i, ((a i) ^ (1 / 3 : ℝ)) ) := by
        rw [Finset.prod_mul_distrib]
      _ = (3 ^ n : ℝ) * (∏ i, (a i) ^ (1 / 3 : ℝ)) := by
        simp [Finset.prod_const]

  have h9 : ∏ i, (a i) ^ (1 / 3 : ℝ) = 1 := by
    have h10 : ∏ i, (a i) ^ (1 / 3 : ℝ) = (∏ i, a i) ^ (1 / 3 : ℝ) := by
      rw [Real.finset_prod_rpow]
      intro i hi
      have ha_pos : 0 < a i := ha i
      positivity
    rw [h10, h]
    have h14 : (1 : ℝ) ^ (1 / 3 : ℝ) = 1 := by
      rw [Real.one_rpow]
    linarith

  have h10 : ∏ i, (3 * (a i) ^ (1 / 3 : ℝ)) = (3 ^ n : ℝ) := by
    rw [h8, h9]
    all_goals norm_num

  linarith