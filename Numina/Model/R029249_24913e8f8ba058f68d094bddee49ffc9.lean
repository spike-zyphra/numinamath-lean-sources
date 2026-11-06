import Mathlib

open Real

theorem number_theory_1413 : (Finset.sum (Finset.range 2003) (fun i => ⌊Real.sqrt ((i + 1) * (i + 2))⌋)) / 1002 = 2003 := by
  have h1 : ∀ i : ℕ, ⌊Real.sqrt ((i + 1 : ℝ) * (i + 2 : ℝ))⌋ = (i + 1 : ℤ) := by
    intro i 
    have h2 : (i + 1 : ℝ) ≤ Real.sqrt ((i + 1 : ℝ) * (i + 2 : ℝ)) := by
      have h4 : ((i + 1 : ℝ) ) ^ 2 ≤ (i + 1 : ℝ) * (i + 2 : ℝ) := by
        nlinarith 
      have h5 : (i + 1 : ℝ) ≤ Real.sqrt ((i + 1 : ℝ) * (i + 2 : ℝ)) := by
        nlinarith [Real.sqrt_nonneg ((i + 1 : ℝ) * (i + 2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (i + 1 : ℝ) * (i + 2 : ℝ) by positivity)]
      linarith
    have h3 : Real.sqrt ((i + 1 : ℝ) * (i + 2 : ℝ)) < (i + 2 : ℝ) := by
      have h6 : (i + 1 : ℝ) * (i + 2 : ℝ) < (i + 2 : ℝ) ^ 2 := by
        nlinarith 
      have h7 : Real.sqrt ((i + 1 : ℝ) * (i + 2 : ℝ)) < (i + 2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg ((i + 1 : ℝ) * (i + 2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (i + 1 : ℝ) * (i + 2 : ℝ) by positivity)]
      linarith 
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith [Real.sqrt_nonneg ((i + 1 : ℝ) * (i + 2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (i + 1 : ℝ) * (i + 2 : ℝ) by positivity)]
  
  have h3 : Finset.sum (Finset.range 2003) (fun i => ⌊Real.sqrt ((i + 1) * (i + 2))⌋) = ∑ i in Finset.range 2003, (i + 1 : ℤ) := by 
    apply Finset.sum_congr 
    · -- Show that the set of indices is the same
      rfl 
    · -- Show that the function applied to each index is the same 
      intro i hi 
      specialize h1 i 
      simpa [h1]
  
  rw [h3] 
  native_decide