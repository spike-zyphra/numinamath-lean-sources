import Mathlib

open Real

theorem algebra_272284 {t : ℕ → ℝ}
    (ht : ∀ n, t n = 1 / n - 1 / (n + 2)) :
    IsGreatest {k | ∑ i in Finset.Icc 1 k, t i < 1.499} 1998 := by
  have h1 : ∀ k : ℕ, ∑ i in Finset.Icc 1 k, t i = (1 : ℝ) + (1 / 2 : ℝ) - (1 / ((k : ℝ) + 1 : ℝ) + 1 / ((k : ℝ) + 2 : ℝ)) := by 
    intro k
    induction k with 
    | zero =>
      simp 
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      simp [ht]
      field_simp 
      ring 
  have h2 : 1998 ∈ {k | ∑ i in Finset.Icc 1 k, t i < 1.499} := by
    rw [Set.mem_setOf_eq]
    rw [h1 1998]
    norm_num
    <;> linarith
  have h3 : ∀ k, k ∈ {k | ∑ i in Finset.Icc 1 k, t i < 1.499} → k ≤ 1998 := by
    intro k hk
    have h4 : ∑ i in Finset.Icc 1 k, t i < 1.499 := by 
      simpa using hk
    by_contra h
    push_neg at h
    have hk1 : k ≥ 1999 := by 
      omega
    have h5 : ∑ i in Finset.Icc 1 k, t i ≥ 1.499 := by
      rw [h1 k]
      have hk11 : (k : ℝ) ≥ (1999 : ℝ) := by
        exact_mod_cast (show k ≥ 1999 by omega)
      have hfrac : (1 / ((k : ℝ) + 1 : ℝ) + 1 / ((k : ℝ) + 2 : ℝ)) ≤ (1 / (2000 : ℝ) + 1 / (2001 : ℝ)) := by
        have h11 : (k : ℝ) + 1 ≥ (2000 : ℝ) := by
          have hk11 : (k : ℝ) ≥ (1999 : ℝ) := by
            exact_mod_cast (show k ≥ 1999 by omega)
          nlinarith
        have h111 : (k : ℝ) + 2 ≥ (2001 : ℝ) := by
          have hk11 : (k : ℝ) ≥ (1999 : ℝ) := by
            exact_mod_cast (show k ≥ 1999 by omega)
          nlinarith
        have h3 : 1 / ((k : ℝ) + 1 : ℝ) ≤ 1 / (2000 : ℝ) := by
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          nlinarith
        have h4 : 1 / ((k : ℝ) + 2 : ℝ) ≤ 1 / (2001 : ℝ) := by
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          nlinarith
        linarith
      linarith [hfrac]
    linarith
  exact ⟨h2, h3⟩