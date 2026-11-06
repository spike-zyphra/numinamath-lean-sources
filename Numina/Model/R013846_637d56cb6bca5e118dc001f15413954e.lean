import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_15753 {f : ℝ → ℝ}
  (hf : ∀ x, x < 4 → f x = x - 2)
  (hf' : ∀ x, x ≥ 4 → f x = sqrt x)
  (f_inv : ℝ → ℝ) (h_finv: ∀ x, f_inv (f x) = x) :
  ∑ i ∈ Finset.range 11, f_inv (i - 5) = 54 := by

  have h2 : ∀ y, f_inv y = if y < (2 : ℝ) then y + 2 else y ^ 2 := by
    intro y
    by_cases hy : y < (2 : ℝ)
    · -- Case y < 2
      have h : f_inv y = y + 2 := by
        have h5 : f (y + 2) = y := by
          have h7 : (y + 2 : ℝ) < (4 : ℝ) := by nlinarith
          have h8 : f (y + 2) = (y + 2) - 2 := hf (y + 2) h7
          have h9 : (y + 2 : ℝ) - (2 : ℝ) = (y : ℝ) := by nlinarith
          rw [h8]
          all_goals nlinarith
        have h6 : f_inv (f (y + 2)) = (y + 2 : ℝ) := by
          apply h_finv
        have h7 : f_inv (f (y + 2)) = f_inv y := by
          rw [h5]
        linarith [h6, h7]
      simp [hy, h]
    · -- Case y ≥ 2
      have h : f_inv y = y ^ 2 := by
        have h5 : f (y ^ 2) = y := by
          rw [hf' (y ^ 2) (by nlinarith)]
          have h6 : sqrt (y ^ 2) = (y : ℝ) := by
            rw [Real.sqrt_sq]
            all_goals nlinarith
          rw [h6]
        have h6 : f_inv (f (y ^ 2)) = (y ^ 2 : ℝ) := by
          apply h_finv
        have h7 : f_inv (f (y ^ 2)) = f_inv y := by
          rw [h5]
        linarith [h6, h7]
      simp [show ¬ (y < (2 : ℝ) ) by linarith, h]
  norm_num [Finset.sum_range_succ, h2]
  all_goals norm_num