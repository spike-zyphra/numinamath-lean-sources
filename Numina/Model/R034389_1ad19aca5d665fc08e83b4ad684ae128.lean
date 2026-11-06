import Mathlib

open Real

theorem inequalities_86499 (n : ℕ) (hn : 2 ≤ n) :
    (∑ i in Finset.Icc 1 n, (i / (n + 1 : ℝ))) ^ ((1 : ℝ) / n) ≥ 1 := by  
  have h2 : ∀ n : ℕ, ∑ i in Finset.Icc 1 n, (i : ℝ) = (n : ℝ) * (n + 1) / 2 := by 
    intro n 
    induction n with 
    | zero => 
      simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      field_simp
      ring_nf
      <;> norm_num
  have h5 : ∑ i in Finset.Icc 1 n, (i / (n + 1 : ℝ)) ≥ (1 : ℝ) := by 
    have h23 : ∑ i in Finset.Icc 1 n, (i / (n + 1 : ℝ)) = (n : ℝ) / 2 := by 
      have h3 : ∑ i in Finset.Icc 1 n, (i / (n + 1 : ℝ)) = (∑ i in Finset.Icc 1 n, (i : ℝ)) / (n + 1 : ℝ) := by
        rw [Finset.sum_div]
      rw [h3]
      rw [h2 n]
      field_simp
      <;> ring_nf 
    rw [h23]
    have h6 : (n : ℝ) ≥ (2 : ℝ) := by exact_mod_cast (show 2 ≤ n by linarith)
    nlinarith 
  have h6 : (∑ i in Finset.Icc 1 n, (i / (n + 1 : ℝ))) ^ ((1 : ℝ) / n) ≥ 1 := by 
    have h7 : ∑ i in Finset.Icc 1 n, (i / (n + 1 : ℝ)) ≥ (1 : ℝ) := by 
      nlinarith 
    have h9 : (∑ i in Finset.Icc 1 n, (i / (n + 1 : ℝ))) ^ ((1 : ℝ) / n) ≥ (1 : ℝ) ^ ((1 : ℝ) / n) := by 
      have h9_1 : (1 : ℝ) / n > 0 := by 
        have : (n : ℝ) ≥ (2 : ℝ) := by exact_mod_cast hn
        have : (n : ℝ) > (0 : ℝ) := by linarith 
        positivity 
      have hbase : ∑ i in Finset.Icc 1 n, (i / (n + 1 : ℝ)) ≥ (1 : ℝ) := h7 
      apply Real.rpow_le_rpow 
      all_goals nlinarith 
      all_goals nlinarith 
    have h9_eq : (1 : ℝ) ^ ((1 : ℝ) / n) = 1 := by 
      simp 
    linarith [h9, h9_eq] 
  linarith