import Mathlib

theorem algebra_303904 {f : ℝ → ℝ} (hf : ∀ x y, 1 < x ∧ x < y → f (1 / x) - f (1 / y) = f ((x - y) / (1 - x * y))) (a : ℕ → ℝ) (ha : ∀ n, 0 < n → a n = f (1 / (n ^ 2 + 5 * n + 5))) :
    ∑ i ∈ Finset.Icc 1 8, a i = f (1 / 4) := by

  have eq1 : a 1 = f (1 / (3 : ℝ)) - f (1 / (4 : ℝ)) := by
    have h1' : a 1 = f (1 / ((1 : ℕ) ^ 2 + 5 * (1 : ℕ) + 5 : ℝ)) := by
      apply ha 1
      all_goals norm_num
    norm_num at h1'
    have eq1' : f (1 / (3 : ℝ)) - f (1 / (4 : ℝ)) = f (1 / ((1 : ℕ) ^ 2 + 5 * (1 : ℕ) + 5 : ℝ)) := by
      have h2 := hf (3 : ℝ) (4 : ℝ) (by constructor <;> norm_num)
      norm_num at h2 ⊢
      linarith
    linarith [h1', eq1']
  have eq2 : a 2 = f (1 / (4 : ℝ)) - f (1 / (5 : ℝ)) := by
    have h1' : a 2 = f (1 / ((2 : ℕ) ^ 2 + 5 * (2 : ℕ) + 5 : ℝ)) := by
      apply ha 2
      all_goals norm_num
    norm_num at h1'
    have eq2' : f (1 / (4 : ℝ)) - f (1 / (5 : ℝ)) = f (1 / ((2 : ℕ) ^ 2 + 5 * (2 : ℕ) + 5 : ℝ)) := by
      have h2 := hf (4 : ℝ) (5 : ℝ) (by constructor <;> norm_num)
      norm_num at h2 ⊢
      linarith
    linarith [h1', eq2']
  have eq3 : a 3 = f (1 / (5 : ℝ)) - f (1 / (6 : ℝ)) := by
    have h1' : a 3 = f (1 / ((3 : ℕ) ^ 2 + 5 * (3 : ℕ) + 5 : ℝ)) := by
      apply ha 3
      all_goals norm_num
    norm_num at h1'
    have eq3' : f (1 / (5 : ℝ)) - f (1 / (6 : ℝ)) = f (1 / ((3 : ℕ) ^ 2 + 5 * (3 : ℕ) + 5 : ℝ)) := by
      have h2 := hf (5 : ℝ) (6 : ℝ) (by constructor <;> norm_num)
      norm_num at h2 ⊢
      linarith
    linarith [h1', eq3']
  have eq4 : a 4 = f (1 / (6 : ℝ)) - f (1 / (7 : ℝ)) := by
    have h1' : a 4 = f (1 / ((4 : ℕ) ^ 2 + 5 * (4 : ℕ) + 5 : ℝ)) := by
      apply ha 4
      all_goals norm_num
    norm_num at h1'
    have eq4' : f (1 / (6 : ℝ)) - f (1 / (7 : ℝ)) = f (1 / ((4 : ℕ) ^ 2 + 5 * (4 : ℕ) + 5 : ℝ)) := by
      have h2 := hf (6 : ℝ) (7 : ℝ) (by constructor <;> norm_num)
      norm_num at h2 ⊢
      linarith
    linarith [h1', eq4']
  have eq5 : a 5 = f (1 / (7 : ℝ)) - f (1 / (8 : ℝ)) := by
    have h1' : a 5 = f (1 / ((5 : ℕ) ^ 2 + 5 * (5 : ℕ) + 5 : ℝ)) := by
      apply ha 5
      all_goals norm_num
    norm_num at h1'
    have eq5' : f (1 / (7 : ℝ)) - f (1 / (8 : ℝ)) = f (1 / ((5 : ℕ) ^ 2 + 5 * (5 : ℕ) + 5 : ℝ)) := by
      have h2 := hf (7 : ℝ) (8 : ℝ) (by constructor <;> norm_num)
      norm_num at h2 ⊢
      linarith
    linarith [h1', eq5']
  have eq6 : a 6 = f (1 / (8 : ℝ)) - f (1 / (9 : ℝ)) := by
    have h1' : a 6 = f (1 / ((6 : ℕ) ^ 2 + 5 * (6 : ℕ) + 5 : ℝ)) := by
      apply ha 6
      all_goals norm_num
    norm_num at h1'
    have eq6' : f (1 / (8 : ℝ)) - f (1 / (9 : ℝ)) = f (1 / ((6 : ℕ) ^ 2 + 5 * (6 : ℕ) + 5 : ℝ)) := by
      have h2 := hf (8 : ℝ) (9 : ℝ) (by constructor <;> norm_num)
      norm_num at h2 ⊢
      linarith
    linarith [h1', eq6']
  have eq7 : a 7 = f (1 / (9 : ℝ)) - f (1 / (10 : ℝ)) := by
    have h1' : a 7 = f (1 / ((7 : ℕ) ^ 2 + 5 * (7 : ℕ) + 5 : ℝ)) := by
      apply ha 7
      all_goals norm_num
    norm_num at h1'
    have eq7' : f (1 / (9 : ℝ)) - f (1 / (10 : ℝ)) = f (1 / ((7 : ℕ) ^ 2 + 5 * (7 : ℕ) + 5 : ℝ)) := by
      have h2 := hf (9 : ℝ) (10 : ℝ) (by constructor <;> norm_num)
      norm_num at h2 ⊢
      linarith
    linarith [h1', eq7']
  have eq8 : a 8 = f (1 / (10 : ℝ)) - f (1 / (11 : ℝ)) := by
    have h1' : a 8 = f (1 / ((8 : ℕ) ^ 2 + 5 * (8 : ℕ) + 5 : ℝ)) := by
      apply ha 8
      all_goals norm_num
    norm_num at h1'
    have eq8' : f (1 / (10 : ℝ)) - f (1 / (11 : ℝ)) = f (1 / ((8 : ℕ) ^ 2 + 5 * (8 : ℕ) + 5 : ℝ)) := by
      have h2 := hf (10 : ℝ) (11 : ℝ) (by constructor <;> norm_num)
      norm_num at h2 ⊢
      linarith
    linarith [h1', eq8']
  have h2 : f (1 / (3 : ℝ)) - f (1 / (11 : ℝ)) = f (1 / (4 : ℝ)) := by
    have h3 := hf (3 : ℝ) (11 : ℝ) (by constructor <;> norm_num)
    norm_num at h3 ⊢
    linarith
  have h3 : f (1 / (3 : ℝ)) - f (1 / (11 : ℝ)) = f (1 / (4 : ℝ)) := h2
  have h4 : ∑ i in Finset.Icc 1 8, a i = (f (1 / (3 : ℝ)) - f (1 / (11 : ℝ)) ) := by
    simp [Finset.sum_Icc_succ_top, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8]
    all_goals norm_num
    all_goals linarith
  linarith [h4, h3]