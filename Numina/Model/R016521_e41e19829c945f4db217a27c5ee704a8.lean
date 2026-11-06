import Mathlib

open Real

theorem algebra_184786 {n : ℕ} (hn : 2 ≤ n) :
    ∏ i ∈ Finset.Icc 2 n, logb i ((1 : ℝ) / i) = (-1) ^ (n - 1) := by

  -- First, show that each term in the product is equal to -1.
  have h1 : ∀ i : ℕ, 2 ≤ i → logb i ((1 : ℝ) / i) = -1 := by
    intro i hi
    have h2 : (i : ℝ) ≥ (2 : ℝ) := by exact_mod_cast hi
    have h3 : logb (i : ℝ) ((1 : ℝ) / (i : ℝ)) = (log ((1 : ℝ) / (i : ℝ)) ) / (log (i : ℝ)) := by 
      field_simp [logb]
    rw [h3]
    have h4 : log ((1 : ℝ) / (i : ℝ)) = - log (i : ℝ) := by 
      rw [log_div (by linarith) (by linarith)]
      norm_num
      <;> linarith
    rw [h4]
    have h5 : log (i : ℝ) ≠ 0 := by
      have h6 : (i : ℝ) ≥ (2 : ℝ) := by exact_mod_cast hi
      have h7 : (i : ℝ) > 1 := by linarith
      have h8 : log (i : ℝ) > 0 := by 
        apply log_pos
        linarith
      linarith
      all_goals linarith
    field_simp [h5]
    <;> ring_nf
    <;> field_simp [h5]

  -- Show that each term in the product index is -1
  have h2 : ∀ i ∈ Finset.Icc 2 n, logb i ((1 : ℝ) / i) = -1 := by 
    intro i hi
    have h3 : 2 ≤ i := by 
      have h4 : i ∈ Finset.Icc 2 n := hi 
      simp at h4 
      omega 
    apply h1 i h3
  -- Convert the term from `log b (1 / i)` to `-1`.
  have h3 : ∏ i ∈ Finset.Icc 2 n, logb i ((1 : ℝ) / i) = 
          ∏ i ∈ Finset.Icc 2 n, (-1 : ℝ) := by 
    apply Finset.prod_congr 
    · -- Show that the index set is the same
      rfl 
    · -- Show that each term is equal
      intro i hi 
      exact h2 i hi 
  rw [h3]
  have h4 : ∏ i ∈ Finset.Icc 2 n, (-1 : ℝ) = (-1) ^ (n - 1) := by
    rw [Finset.prod_const]
    have h6 : (Finset.Icc 2 n).card = n - 1 := by
      have h7 : 2 ≤ n := hn 
      simp at *
      <;> try { 
        have : n ≥ 2 := by omega
        omega 
      }
      <;> try { 
        tauto 
      }
    rw [h6]
    <;> try { simp }
    all_goals try omega
  rw [h4]
  all_goals try omega