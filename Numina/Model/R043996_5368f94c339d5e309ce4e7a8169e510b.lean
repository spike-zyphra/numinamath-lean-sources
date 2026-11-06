import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_11516 {p : ℝ} (hp : p > 0) (h : ℝ → ℝ)
  (h_def : h = λ x => ((1 - x ^ p) / (1 + 0 * x ^ p)) ^ (1 / p))
  (h1 : ∀ x ∈ Ioo 0 1, h x > 1 - x) :
  1 < p := by
  by_contra h2
  push_neg at h2
  have h3 := h1 ((1 / 2 : ℝ) ^ (1 / p)) (by
    constructor
    · -- Show that 0 < (1/2)^(1/p)
      have h4 : (1 / 2 : ℝ) ^ (1 / p : ℝ) > (0 : ℝ) := by positivity
      linarith
    · -- Show that (1/2)^(1/p) < 1
      have h5 : (1 / 2 : ℝ) ^ (1 / p : ℝ) < (1 : ℝ) := by
        have h6 : (1 / 2 : ℝ) ^ (1 / p : ℝ) < (1 / 2 : ℝ) ^ (0 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_gt
          all_goals
            try linarith
            try norm_num
            all_goals linarith
        have h7 : (1 / 2 : ℝ) ^ (0 : ℝ) = (1 : ℝ) := by
          simp
        have h8 : (1 / 2 : ℝ) ^ (1 / p : ℝ) < (1 : ℝ) := by
          linarith [h6, h7]
        linarith
      all_goals nlinarith
    )
  have eq : h ((1 / 2 : ℝ) ^ (1 / p)) = ((1 - ((1 / 2 : ℝ) ^ (1 / p)) ^ p) / (1 + (0 : ℝ) * ((1 / 2 : ℝ) ^ (1 / p)) ^ p)) ^ (1 / p : ℝ) := by
    rw [h_def]
    all_goals norm_num
  rw [eq] at h3
  have h6 : ((1 / 2 : ℝ) ^ (1 / p : ℝ)) ^ p = (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul]
    field_simp at *
    all_goals linarith
    all_goals norm_num
    all_goals norm_num
  have h7 : (1 - ((1 / 2 : ℝ) ^ (1 / p : ℝ)) ^ p) = (1 / 2 : ℝ) := by
    rw [h6]
    all_goals norm_num
  have h8 : ((1 - ((1 / 2 : ℝ) ^ (1 / p : ℝ)) ^ p) / (1 + (0 : ℝ) * ((1 / 2 : ℝ) ^ (1 / p : ℝ)) ^ p)) ^ (1 / p : ℝ) = ((1 / 2 : ℝ) ) ^ (1 / p : ℝ) := by
    rw [h7]
    all_goals norm_num
    <;> ring_nf <;> norm_num
    all_goals norm_num
  rw [h8] at h3
  have h11 : ((1 / 2 : ℝ) ^ (1 / p : ℝ)) > (1 / 2 : ℝ) := by
    nlinarith
  have h12 : (1 / p : ℝ) < (1 : ℝ) := by
    by_contra h13
    push_neg at h13
    have h14 : (1 / 2 : ℝ) ^ (1 / p : ℝ) ≤ (1 / 2 : ℝ) ^ (1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_ge
      all_goals
        try linarith
        try positivity
        all_goals linarith
    have h15 : (1 / 2 : ℝ) ^ (1 : ℝ) = (1 / 2 : ℝ) := by
      norm_num
    have h16 : (1 / 2 : ℝ) ^ (1 / p : ℝ) ≤ (1 / 2 : ℝ) := by
      linarith [h14, h15]
    linarith [h11, h16]
  -- From h12 (1/p < 1), we derive 1 < p
  have h17 : (1 / p : ℝ) > (0 : ℝ) := by positivity
  have h18 : p > (0 : ℝ) := by linarith
  have h19 : p > (1 : ℝ) := by
    by_contra h20
    push_neg at h20
    have h21 : p ≤ (1 : ℝ) := by linarith
    have h22 : (1 / p : ℝ) ≥ (1 : ℝ) := by
      have h23 : (1 / p : ℝ) ≥ (1 : ℝ) := by
        apply (le_div_iff₀ (by linarith)).mpr
        nlinarith
      linarith
    linarith [h12, h22]
  linarith [h19, h2]