import Mathlib

theorem algebra_130950 {b : ℕ → ℝ} (hb : ∃ r, ∀ n, b n = b 0 * r ^ n)
    (hpos : ∀ n, b n > 0) (hsum : ∑ i in Finset.Icc 8 2020, b i ^ 2 = 4)
    (hrec : ∑ i in Finset.Icc 8 2020, 1 / b i ^ 2 = 1) :
    ∏ i in Finset.Icc 8 2020, b i ^ 2 = 2 ^ 2013 := by
  have h4 : ∑ i in Finset.Icc 8 2020, b i ^ 2 + ∑ i in Finset.Icc 8 2020, (1 / b i ^ 2) ≥ (4026 : ℝ) := by
    have h5 : ∀ i ∈ Finset.Icc 8 2020, b i ^ 2 + (1 / b i ^ 2) ≥ (2 : ℝ) := by
      intro i hi
      have hbi : b i > 0 := hpos i
      have hb2i : b i ^ 2 > 0 := by positivity
      have h11 : b i ^ 2 + (1 / b i ^ 2) ≥ (2 : ℝ) := by
        have h12 : b i ^ 2 + (1 / b i ^ 2) - (2 : ℝ) ≥ (0 : ℝ) := by
          have h13 : b i ^ 2 + (1 / b i ^ 2) - (2 : ℝ) = (b i ^ 2 - (1 : ℝ)) ^ 2 / b i ^ 2 := by 
            field_simp
            <;> ring
          rw [h13]
          apply div_nonneg
          · -- Show that (b i ^ 2 - 1) ^ 2 ≥ 0 
            positivity
          · -- Show that b i ^ 2 > 0 
            positivity
        linarith
      linarith
    have h6 : (∑ i in Finset.Icc 8 2020, b i ^ 2) + (∑ i in Finset.Icc 8 2020, (1 / b i ^ 2)) ≥ (4026 : ℝ) := by
      have h7 : (∑ i in Finset.Icc 8 2020, b i ^ 2) + (∑ i in Finset.Icc 8 2020, (1 / b i ^ 2)) = (∑ i in Finset.Icc 8 2020, (b i ^ 2 + (1 / b i ^ 2)) ) := by 
        rw [Finset.sum_add_distrib]
      rw [h7]
      have h8 : (Finset.Icc 8 2020).card = 2013 := by 
        native_decide
      have h9 : (∑ i in Finset.Icc 8 2020, (b i ^ 2 + (1 / b i ^ 2)) ) ≥ (4026 : ℝ) := by 
        have h10 : (∑ i in Finset.Icc 8 2020, (b i ^ 2 + (1 / b i ^ 2)) ) ≥ ∑ i in Finset.Icc 8 2020, (2 : ℝ) := by 
          apply Finset.sum_le_sum 
          intro i hi
          specialize h5 i hi 
          linarith 
        have h11 : ∑ i in Finset.Icc 8 2020, (2 : ℝ) = (4026 : ℝ) := by 
          rw [Finset.sum_const, h8]
          all_goals norm_num 
        linarith [h10, h11] 
      linarith [h9]
    linarith [h6]
  have h5 : (4 + 1 : ℝ) ≥ (4026 : ℝ) := by
    have eq1 : (∑ i in Finset.Icc 8 2020, b i ^ 2) = (4 : ℝ) := by
      linarith [hsum]
    have eq2 : (∑ i in Finset.Icc 8 2020, (1 / b i ^ 2) ) = (1 : ℝ) := by
      linarith [hrec]
    linarith [h4, eq1, eq2]
  nlinarith