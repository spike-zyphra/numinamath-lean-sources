import Mathlib

theorem number_theory_15056 {n : ℕ} (hn : n = 522) :
    18 ∣ n ∧ 8 < (n : ℝ) ^ ((1 : ℝ) / 3) ∧ (n : ℝ) ^ ((1 : ℝ) / 3) < 8.1 := by
  subst hn
  constructor
  · -- Show 18 divides 522
    norm_num
  constructor
  · -- Show 8 < (522 : ℝ) ^ ((1 : ℝ) / 3)
    have h1 : (522 : ℝ) ^ ((1 : ℝ) / 3) > (8 : ℝ) := by
      have h2 : (522 : ℝ) > (8 : ℝ) ^ (3 : ℝ) := by
        norm_num
      have h4 : (522 : ℝ) ^ ((1 : ℝ) / 3) > ( (8 : ℝ) ^ (3 : ℝ) ) ^ ((1 : ℝ) / 3) := by
        apply Real.rpow_lt_rpow
        all_goals
          nlinarith
      have h5 : ( (8 : ℝ) ^ (3 : ℝ) ) ^ ((1 : ℝ) / 3) = (8 : ℝ) := by
        rw [← Real.rpow_mul]
        norm_num
        all_goals
          norm_num
      linarith [h4, h5]
    linarith
  · -- Show (522 : ℝ) ^ ((1 : ℝ) / 3) < (8.1 : ℝ)
    have h1 : (522 : ℝ) ^ ((1 : ℝ) / 3) < (8.1 : ℝ) := by
      have h2 : (522 : ℝ) < (8.1 : ℝ) ^ (3 : ℝ) := by
        norm_num
      have h4 : (522 : ℝ) ^ ((1 : ℝ) / 3) < ( (8.1 : ℝ) ^ (3 : ℝ) ) ^ ((1 : ℝ) / 3) := by
        apply Real.rpow_lt_rpow
        all_goals
          nlinarith
      have h5 : ( (8.1 : ℝ) ^ (3 : ℝ) ) ^ ((1 : ℝ) / 3) = (8.1 : ℝ) := by
        rw [← Real.rpow_mul]
        norm_num
        all_goals
          norm_num
      linarith [h4, h5]
    linarith