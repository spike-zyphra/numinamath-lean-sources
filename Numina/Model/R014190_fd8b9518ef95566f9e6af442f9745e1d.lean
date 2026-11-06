import Mathlib


theorem algebra_600962 {f : ℝ → ℝ} (hf : ∀ x ∈ Set.Icc 1 2001, f (x / 2001) = x / 2001) :
    ∑ i ∈ Finset.range 2000, f ((2000 - i) / 2001) = 1000 := by
  have h2 : ∑ i in Finset.range 2000, f ((2000 - i : ℝ) / 2001) = ∑ i in Finset.range 2000, ((2000 - i : ℝ) / 2001) := by
    apply Finset.sum_congr
    . rfl
    intro i hi
    have hk5 : (2000 - i : ℝ) ∈ Set.Icc (1 : ℝ) (2001 : ℝ) := by
      have hk1 : (1 : ℝ) ≤ (2000 - i : ℝ) := by
        have h3 : (i : ℝ) ≤ (1999 : ℝ) := by
          have h3 : i ≤ 1999 := by
            simp at *
            all_goals omega
          exact_mod_cast h3
        nlinarith
      have hk2 : (2000 - i : ℝ) ≤ (2001 : ℝ) := by
        have h3 : (i : ℝ) ≥ (0 : ℝ) := by
          have h3 : i ≥ 0 := by
            omega
          exact_mod_cast h3
        nlinarith
      exact ⟨by linarith, by linarith⟩
    specialize hf (2000 - i : ℝ) hk5
    simpa using hf
  rw [h2]
  norm_num [Finset.sum_range_succ]