import Mathlib

open Real

theorem inequalities_233502 (k : ℝ) :
    (∀ m n : ℕ, 0 < m → 0 < n → (1 / (m + n)) ^ 2 ≤ k * (1 / m ^ 2 + 1 / n ^ 2)) ↔
    k ≥ 1 / 8 := by
  constructor
  · -- First, we show that if the inequality holds for all m, n, then k ≥ 1/8.
    intro h
    have h22 := h 2 2 (by norm_num) (by norm_num)
    norm_num at h22 ⊢
    linarith
  · -- Now, we need to show that if k ≥ 1/8, then the inequality holds for all m, n.
    intro hk m n hm hn
    have h : (1 / (m + n) : ℝ) ^ 2 ≤ (1 / 8) * (1 / (m : ℝ) ^ 2 + 1 / (n : ℝ) ^ 2) := by
      have hm' : m > 0 := hm
      have hn' : n > 0 := hn
      have h1 : (m : ℝ) > 0 := by exact_mod_cast hm
      have h2 : (n : ℝ) > 0 := by exact_mod_cast hn
      have h3 : (m + n : ℝ) > 0 := by
        have hm' : (m : ℝ) > 0 := by exact_mod_cast hm
        have hn' : (n : ℝ) > 0 := by exact_mod_cast hn
        linarith
      have h6 : (1 / (m + n) : ℝ) ^ 2 ≤ (1 / 8) * (1 / (m : ℝ) ^ 2 + 1 / (n : ℝ) ^ 2) := by 
        have h7 : (1 / (m + n) : ℝ) ^ 2 - (1 / 8) * (1 / (m : ℝ) ^ 2 + 1 / (n : ℝ) ^ 2) ≤ 0 := by
          have pos1 : (m : ℝ) ^ 2 > 0 := by positivity
          have pos2 : (n : ℝ) ^ 2 > 0 := by positivity
          have pos3 : ((m + n) : ℝ) ^ 2 > 0 := by
            have h1 : (m : ℝ) > 0 := by exact_mod_cast hm
            have h2 : (n : ℝ) > 0 := by exact_mod_cast hn
            nlinarith [h1, h2]
          have pos4 : (m : ℝ) ^ 2 * (n : ℝ) ^ 2 * ((m + n) : ℝ) ^ 2 > 0 := by positivity
          have h8 : (1 / (m + n) : ℝ) ^ 2 - (1 / 8) * (1 / (m : ℝ) ^ 2 + 1 / (n : ℝ) ^ 2) = 
            (8 * (m : ℝ) ^ 2 * (n : ℝ) ^ 2 - (m^2 + n^2) * ((m + n) : ℝ) ^ 2) / (8 * (m : ℝ) ^ 2 * (n : ℝ) ^ 2 * ((m + n) : ℝ) ^ 2) := by 
            field_simp
            <;> ring
          rw [h8] at *
          apply div_nonpos_of_nonpos_of_nonneg
          · 
            nlinarith [sq_nonneg ((m : ℝ) - (n : ℝ)), sq_nonneg ((m + n) : ℝ), sq_nonneg ((m : ℝ) * (n : ℝ)), sq_nonneg ((m : ℝ) ^ 2 - (n : ℝ) ^ 2), sq_nonneg ((m : ℝ) - (n : ℝ)), sq_nonneg ((m : ℝ) * (n : ℝ) - (m * n : ℝ)), mul_pos (show (0 < (m : ℝ) ) by exact_mod_cast hm) (show (0 < (n : ℝ) ) by exact_mod_cast hn)]
          · 
            positivity
        linarith
      linarith
    have h7 : (1 / (m + n) : ℝ) ^ 2 ≤ k * (1 / (m : ℝ) ^ 2 + 1 / (n : ℝ) ^ 2) := by 
      nlinarith [h, hk]
    exact_mod_cast h7