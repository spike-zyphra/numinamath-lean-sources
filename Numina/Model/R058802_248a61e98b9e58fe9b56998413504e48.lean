import Mathlib

open Real

theorem other_227001 (P : ℕ → ℝ)
    (hP : ∀ n, P n = (1 / (n + 1)) ^ 2) :
    P 1 > P 2 ∧ P 1 > P 5 := by 
  have h1 : P 1 = (1 / 4 : ℝ) := by
    rw [hP]
    norm_num
  have h2 : P 2 = (1 / 9 : ℝ) := by 
    rw [hP]
    norm_num
  have h5 : P 5 = (1 / 36 : ℝ) := by 
    rw [hP]
    norm_num
  constructor
  · -- Prove P 1 > P 2
    rw [h1, h2]
    norm_num
  · -- Prove P 1 > P 5
    rw [h1, h5]
    norm_num