import Mathlib

theorem inequalities_201610 (a : Fin 20 → ℝ) (ha : ∀ i j k, i + 1 = j ∧ j + 1 = k → a i + a j + a k > 0)
    (hsum : ∑ i, a i < 0) :
    False := by

  have h1 := ha 0 1 2 (by simp)
  have h2 := ha 1 2 3 (by simp)
  have h3 := ha 2 3 4 (by simp)
  have h4 := ha 3 4 5 (by simp)
  have h5 := ha 4 5 6 (by simp)
  have h6 := ha 5 6 7 (by simp)
  have h7 := ha 6 7 8 (by simp)
  have h8 := ha 7 8 9 (by simp)
  have h9 := ha 8 9 10 (by simp)
  have h10 := ha 9 10 11 (by simp)
  have h11 := ha 10 11 12 (by simp)
  have h12 := ha 11 12 13 (by simp)
  have h13 := ha 12 13 14 (by simp)
  have h14 := ha 13 14 15 (by simp)
  have h15 := ha 14 15 16 (by simp)
  have h16 := ha 15 16 17 (by simp)
  have h17 := ha 16 17 18 (by simp)
  have h18 := ha 17 18 19 (by simp)
  have h19 := ha 18 19 0 (by simp)
  have h20 := ha 19 0 1 (by simp)
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hsum
  linarith