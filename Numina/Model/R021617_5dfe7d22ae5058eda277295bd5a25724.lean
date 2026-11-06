import Mathlib

theorem algebra_10548 (f : ℕ → ℝ)
    (hf : ∀ n, f n = (∑ i in Finset.Icc 1 n, i) / ((n + 32) * ∑ i in Finset.Icc 1 (n + 1), i)) :
    IsGreatest (Set.image f {n | n + 1 ≥ 1}) (1 / 50) := by
  have h5 : ∀ n : ℕ, f n = (∑ i in Finset.Icc 1 n, (i : ℝ)) / ((n + 32 : ℝ) * ∑ i in Finset.Icc 1 (n + 1), (i : ℝ)) := by 
    intro n 
    specialize hf n 
    simpa using hf 
  have h6 : f 8 = 1 / 50 := by 
    rw [h5 8] 
    norm_num [Finset.sum_Icc_succ_top] 
  constructor
  · -- Show that 1/50 is in the image.
    use 8 
    all_goals 
      constructor
      · -- Show that 8 is in the domain.
        norm_num 
      · -- Show that f 8 = 1/50.
        exact h6 
  · -- Show that 1/50 is the greatest.
    intro r hr 
    rcases hr with ⟨n, hn, h7⟩ 
    have hn1 : n ≥ 0 := by 
      have h8 : n + 1 ≥ 1 := by 
        simpa using hn 
      omega 
    have h8 : f n ≤ 1 / 50 := by
      rw [h5 n] 
      have eq1 : (∑ i in Finset.Icc 1 n, (i : ℝ)) = (n : ℝ) * (n + 1) / 2 := by 
        have h1 : ∀ (n : ℕ), (∑ i in Finset.Icc 1 n, (i : ℝ)) = (n : ℝ) * (n + 1) / 2 := by
          intro n 
          induction n with 
          | zero => 
            simp 
          | succ n ih => 
            rw [Finset.sum_Icc_succ_top (by linarith)]
            simp [ih] 
            <;> field_simp <;> ring 
        specialize h1 n 
        simpa using h1 
      have eq2 : (∑ i in Finset.Icc 1 (n + 1), (i : ℝ)) = (n + 1 : ℝ) * (n + 2 : ℝ) / 2 := by 
        have h1 : ∀ (n : ℕ), (∑ i in Finset.Icc 1 (n + 1), (i : ℝ)) = (n + 1 : ℝ) * (n + 2 : ℝ) / 2 := by 
          intro n 
          induction n with 
          | zero => 
            norm_num 
          | succ n ih => 
            rw [Finset.sum_Icc_succ_top (by linarith)]
            simp [ih] 
            <;> field_simp <;> ring 
        specialize h1 n 
        simpa using h1 
      rw [eq1, eq2] 
      have h9 : (n : ℝ) ≥ 0 := by exact_mod_cast (show n ≥ 0 by omega) 
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg ((n : ℝ) - 8 : ℝ), sq_nonneg ((n : ℝ) + 2 : ℝ), sq_nonneg ((n : ℝ) + 32 : ℝ), mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) by nlinarith) (show (0 : ℝ) ≤ (n + 1: ℝ) by nlinarith)]
    linarith 
  all_goals try { tauto }