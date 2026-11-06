import Mathlib

open Real

theorem inequalities_232805 {n : ℕ} (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (x / y) ^ ((1 : ℝ) / (n + 1)) ≤ (x + n * y) / ((n + 1) * y) := by 
  have h1 : (x + n * y) / ((n + 1) * y) = (x / y) / (n + 1) + n / (n + 1) := by
    field_simp
    <;> ring_nf
  rw [h1]

  by_cases hn : n = 0
  · -- Case n = 0
    rw [hn]
    norm_num
  · -- Case n ≠ 0
    have hn1 : n > 0 := by
      omega 
    have h21 : (x / y : ℝ) / (n + 1) + (n / (n + 1) : ℝ) = (1 / ((n : ℝ) + 1)) * (x / y) + (n / ((n : ℝ) + 1)) * (1 : ℝ) := by 
      field_simp 
      <;> ring_nf 
    rw [h21]

    have h_nonneg : (x / y : ℝ) ≥ 0 := by 
      apply div_nonneg 
      linarith 
      linarith 
    have hn_pos : (n : ℝ) > (0 : ℝ) := by
      exact_mod_cast (show (n : ℕ) > 0 by omega)
    have hn1_pos : (n + 1 : ℝ) > (0 : ℝ) := by 
      nlinarith 
    have hw1_nonneg : (1 / ((n : ℝ) + 1) ) ≥ 0 := by 
      positivity 
    have hw2_nonneg : (n / ((n : ℝ) + 1) ) ≥ 0 := by 
      apply div_nonneg 
      nlinarith 
      all_goals nlinarith 
    have hwsum : (1 / ((n : ℝ) + 1) ) + (n / ((n : ℝ) + 1) ) = 1 := by 
      field_simp 
      nlinarith

    have h37 : (x / y) ^ ((1 : ℝ) / (↑n + 1)) ≤ (1 / ((n : ℝ) + 1)) * (x / y) + (n / ((n : ℝ) + 1)) * (1 : ℝ) := by 
      have h53 : ((x / y) : ℝ) ^ ((1 / ((n : ℝ) + 1) : ℝ) ) * ((1 : ℝ) ^ ((n / ((n : ℝ) + 1) : ℝ) ) ) ≤ (1 / ((n : ℝ) + 1) ) * (x / y) + (n / ((n : ℝ) + 1) ) * (1 : ℝ) := by
        apply Real.geom_mean_le_arith_mean2_weighted 
        all_goals
          try positivity 
          all_goals 
            try { 
              have hn_pos : (n : ℝ) > (0 : ℝ) := hn_pos
              have hn1_pos : (n + 1 : ℝ) > (0 : ℝ) := hn1_pos 
              field_simp
              <;> linarith
            }
      have h48 : ((1 : ℝ) ^ ((n / ((n : ℝ) + 1) : ℝ) ) ) = (1 : ℝ) := by 
        rw [Real.one_rpow]
      have h56 : ((x / y) : ℝ) ^ ((1 / ((n : ℝ) + 1) : ℝ) ) ≤ (1 / ((n : ℝ) + 1) ) * (x / y) + (n / ((n : ℝ) + 1) ) * (1 : ℝ) := by 
        have h50 : ((x / y) : ℝ) ^ ((1 / ((n : ℝ) + 1) : ℝ) ) * ((1 : ℝ) ^ ( (n / ((n : ℝ) + 1) : ℝ) ) ) ≤ (1 / ((n : ℝ) + 1) ) * (x / y) + (n / ((n : ℝ) + 1) ) * (1 : ℝ) := h53 
        rw [h48] at h50 
        nlinarith 
      linarith

    linarith [h37]