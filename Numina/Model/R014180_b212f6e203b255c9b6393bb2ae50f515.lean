import Mathlib

open Real

theorem algebra_161394 {p : ℕ → ℝ} (hp : ∀ d, p d = log (d + 1) - log d)
    (h : p 2 = -1 / 2 * ∑ d ∈ Finset.Icc 3 8, p d) :
    p 2 = -1 / 2 * ∑ d ∈ Finset.Icc 4 8, p d := by

  have hp2 : p 2 = log 3 - log 2 := by
    rw [hp 2]
    all_goals norm_num
    <;> try simp [log_div]
    <;> try linarith

  have hsum : ∑ d in Finset.Icc 3 8, p d = log 3 := by
    have h1 : ∑ d in Finset.Icc 3 8, p d = (p 3 + p 4 + p 5 + p 6 + p 7 + p 8) := by
      simp [Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top, mul_add, add_mul]
      <;> try rfl
      <;> try norm_num
      <;> try linarith
    rw [h1]
    have hp3 : p 3 = log 4 - log 3 := by
      rw [hp 3]
      all_goals norm_num
    have hp4 : p 4 = log 5 - log 4 := by
      rw [hp 4]
      all_goals norm_num
    have hp5 : p 5 = log 6 - log 5 := by
      rw [hp 5]
      all_goals norm_num
    have hp6 : p 6 = log 7 - log 6 := by
      rw [hp 6]
      all_goals norm_num
    have hp7 : p 7 = log 8 - log 7 := by
      rw [hp 7]
      all_goals norm_num
    have hp8 : p 8 = log 9 - log 8 := by
      rw [hp 8]
      all_goals norm_num
    rw [hp3, hp4, hp5, hp6, hp7, hp8]
    have h3 : log 4 - log 3 + (log 5 - log 4) + (log 6 - log 5) + (log 7 - log 6) + (log 8 - log 7) + (log 9 - log 8) = log 9 - log 3 := by
      linarith
    have h4 : log 9 = 2 * log 3 := by
      calc
        log 9 = log (3 ^ 2) := by norm_num
        _ = 2 * log 3 := by simp [log_pow]
    have h2 : log 4 - log 3 + (log 5 - log 4) + (log 6 - log 5) + (log 7 - log 6) + (log 8 - log 7) + (log 9 - log 8) = log 3 := by
      rw [h3, h4]
      all_goals linarith
    linarith [h2]

  rw [hp2, hsum] at h
  have h1 : log 3 - log 2 = -1 / 2 * log 3 := by
    linarith

  -- $ p 2 = \log 3 - \log 2 = -1/2 * \log 3 $ is contradiction
  -- Now, $ \log 3 - \log 2 = -1/2 * \log 3 $
  -- $\log 3 + \log 3 / 2 = \log 2$
  -- $3/2 \cdot \log 3 = \log 2$
  have h2 : (3 / 2) * log 3 = log 2 := by
    linarith

  have h4 : log (3 ^ (3 / 2 : ℝ)) = log (2 : ℝ) := by
    calc
      log (3 ^ (3 / 2 : ℝ)) = (3 / 2 : ℝ) * log (3 : ℝ) := by
        rw [log_rpow]
        all_goals norm_num
      _ = log 2 := by
        linarith [h2]

  have h5 : (3 : ℝ) ^ ((3 / 2 : ℝ) ) = (2 : ℝ) := by
    have h6 : log ((3 : ℝ) ^ ((3 / 2 : ℝ) ) ) = log (2 : ℝ) := by
      linarith [h4]
    have h7 : (3 : ℝ) ^ ((3 / 2 : ℝ) ) = (2 : ℝ) := by
      apply log_injOn_pos (Set.mem_Ioi.mpr (show (0 : ℝ) < (3 : ℝ) ^ (3 / 2 : ℝ) by positivity)) (Set.mem_Ioi.mpr (show 0 < (2 : ℝ) by norm_num)) h6
    linarith

  have h6 : (3 : ℝ) ^ ((3 / 2 : ℝ) ) = (3 : ℝ) * Real.sqrt 3 := by
    have h7 : (3 : ℝ) ^ ((3 / 2 : ℝ) ) = (3 : ℝ) * Real.sqrt 3 := by
      have h8 : (3 : ℝ) ^ ((3 / 2 : ℝ) ) = ((3 : ℝ) ^ (1 : ℝ)) * ((3 : ℝ) ^ ((1 / 2 : ℝ) ) ) := by
        rw [← Real.rpow_add]
        norm_num
        all_goals norm_num
      rw [h8]
      have h9 : (3 : ℝ) ^ ((1 : ℝ) ) = (3 : ℝ) := by
        simp
      have h10 : (3 : ℝ) ^ ((1 / 2 : ℝ) ) = Real.sqrt (3 : ℝ) := by
        rw [← Real.sqrt_eq_rpow]
      rw [h9, h10]
    linarith

  rw [h6] at h5
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]