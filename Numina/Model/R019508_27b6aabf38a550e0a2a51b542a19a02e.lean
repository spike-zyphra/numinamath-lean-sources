import Mathlib

open Real

theorem inequalities_115263 (x : ℝ) (a n : ℕ) (ha : 0 < a) (hn : 0 < n) :
    abs (x + a) + abs (x - a ^ 2) ≥ a ^ 2 + a ∧
    ∑ i ∈ Finset.Icc 1 n, abs (x + i) + ∑ i ∈ Finset.Icc 1 n, abs (x - i ^ 2) ≥
    n * (n + 1) * (n + 2) / 3 := by 
  constructor
  · -- Prove the first inequality for part a
    have h1 : abs (x + (a : ℝ)) + abs (x - (a : ℝ) ^ 2) ≥ (a : ℝ) ^ 2 + (a : ℝ) := by
      have h2 : abs (x + (a : ℝ)) + abs (x - (a : ℝ) ^ 2) ≥ abs ((x + (a : ℝ)) - (x - (a : ℝ) ^ 2)) := by 
        apply abs_sub 
      have h3 : (x + (a : ℝ)) - (x - (a : ℝ) ^ 2) = (a : ℝ) ^ 2 + (a : ℝ) := by 
        ring 
      have h4 : abs ((x + (a : ℝ)) - (x - (a : ℝ) ^ 2)) = abs (( (a : ℝ) ^ 2 + (a : ℝ) )) := by 
        rw [h3]
      rw [h4] at h2 
      have h3a : abs (( (a : ℝ) ^ 2 + (a : ℝ) )) = (a : ℝ) ^ 2 + (a : ℝ) := by 
        have h4a : (a : ℝ) ^ 2 + (a : ℝ) ≥ 0 := by 
          have ha1 : (a : ℝ) ≥ (0 : ℝ) := by exact_mod_cast (show (a : ℕ) ≥ (0 : ℕ) by omega) 
          nlinarith [sq_nonneg ( (a : ℝ) ) ]
        rw [abs_of_nonneg h4a]
      linarith [h2, h3a]
    simpa using h1
  · -- Prove the inequality for part b
    have h2 : ∀ i : ℕ, abs (x + (i : ℝ)) + abs (x - (i : ℝ) ^ 2) ≥ (i : ℝ) ^ 2 + (i : ℝ) := by 
      intro i 
      have h5 : abs (x + (i : ℝ)) + abs (x - (i : ℝ) ^ 2) ≥ (i : ℝ) ^ 2 + (i : ℝ) := by 
        have h6 : abs (x + (i : ℝ)) + abs (x - (i : ℝ) ^ 2) ≥ abs ((x + (i : ℝ)) - (x - (i : ℝ) ^ 2)) := by 
          apply abs_sub
        have h7 : (x + (i : ℝ)) - (x - (i : ℝ) ^ 2) = (i : ℝ) ^ 2 + (i : ℝ) := by 
          ring
        have h8 : abs ((x + (i : ℝ)) - (x - (i : ℝ) ^ 2)) = abs (( (i : ℝ) ^ 2 + (i : ℝ) )) := by 
          rw [h7]
        rw [h8] at h6
        have h9 : abs (( (i : ℝ) ^ 2 + (i : ℝ) )) = (i : ℝ) ^ 2 + (i : ℝ) := by
          have h5a : (i : ℝ) ^ 2 + (i : ℝ) ≥ 0 := by 
            have ha1 : (i : ℝ) ≥ (0 : ℝ) := by exact_mod_cast (show (i : ℕ) ≥ (0 : ℕ) by omega)
            nlinarith [sq_nonneg ( (i : ℝ) ) ]
          rw [abs_of_nonneg h5a]
        linarith [h6, h9]
      linarith
    have h3 : (∑ i ∈ Finset.Icc 1 n, (abs (x + (i : ℝ)) + abs (x - (i : ℝ) ^ 2))) ≥ ∑ i ∈ Finset.Icc 1 n, ((i : ℝ) ^ 2 + (i : ℝ)) := by 
      apply Finset.sum_le_sum 
      intro i hi 
      have h4 : abs (x + (i : ℝ)) + abs (x - (i : ℝ) ^ 2) ≥ (i : ℝ) ^ 2 + (i : ℝ) := h2 i 
      linarith 
    have h5 : (∑ i ∈ Finset.Icc 1 n, ((i : ℝ) ^ 2 + (i : ℝ)) ) = (n * (n + 1) * (n + 2) / 3 : ℝ) := by 
      have h7 : ∀ (n : ℕ), ∑ i ∈ Finset.Icc 1 n, ((i : ℝ) ^ 2 + (i : ℝ)) = (n * (n + 1) * (n + 2) / 3 : ℝ) := by 
        intro n 
        induction n with 
        | zero => 
          simp 
        | succ n ih => 
          rw [Finset.sum_Icc_succ_top (by linarith)]
          rw [ih] 
          field_simp 
          <;> ring 
      specialize h7 n 
      linarith [h7] 
    have h8 : ∑ i ∈ Finset.Icc 1 n, abs (x + (i : ℝ)) + ∑ i ∈ Finset.Icc 1 n, abs (x - (i : ℝ) ^ 2) = ∑ i ∈ Finset.Icc 1 n, (abs (x + (i : ℝ)) + abs (x - (i : ℝ) ^ 2)) := by 
      rw [Finset.sum_add_distrib] 
    rw [h8] 
    linarith [h3, h5]