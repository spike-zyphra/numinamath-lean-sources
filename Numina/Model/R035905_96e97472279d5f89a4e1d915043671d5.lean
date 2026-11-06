import Mathlib
open Real

theorem inequalities_171051 (x : ℝ) (hx : x ≠ -4) (hx1 : logb 6 ((x ^ 2 + x) / (x + 4)) > 0) (hx2 : (x ^ 2 + x) / (x + 4) > 0) : logb 0.3 (logb 6 ((x^2 + x) / (x + 4))) < 0 ↔
x ∈ Set.Ioo (-4) (-3) ∪ Set.Ioi 8:= by
  constructor
  · -- Proof of the forward direction (→)
    intro h
    rw [←Real.log_div_log] at h
    norm_num at h
    have h1 : log (3 / 10) < 0:= by
      have h1 : 0 < (3 : ℝ) / 10:= by linarith
      have h2 : (3 : ℝ) / 10 < 1:= by norm_num
      exact log_neg h1 h2
    rw [show log (logb 6 ((x ^ 2 + x) / (x + 4))) / log (3 / 10) = log (logb 6 ((x ^ 2 + x) / (x + 4))) * (1 / log (3 / 10)) by field_simp] at h
    replace h1 : 1 / log (3 / 10) < 0:= by exact one_div_neg.mpr h1
    replace h : log (logb 6 ((x ^ 2 + x) / (x + 4))) > 0:= by exact (pos_iff_neg_of_mul_neg h).mpr h1
    replace h : logb 6 ((x ^ 2 + x) / (x + 4)) > 1:= by exact (Real.log_pos_iff hx1).1 h
    rw [←Real.log_div_log] at h
    replace h1 : log 6 > 0:= by
      have h2 : (6 : ℝ) > 1:= by norm_num
      exact log_pos h2
    replace h : log ((x ^ 2 + x) / (x + 4)) > log 6:= by exact (one_lt_div h1).mp h
    replace h : (x ^ 2 + x) / (x + 4) > 6:= by
      have h2 : (6 : ℝ) > 0:= by norm_num
      exact (log_lt_log_iff h2 hx2).mp h
    replace h : (x ^ 2 + x) / (x + 4) - 6 > 0:= by linarith
    have gx : x + 4 ≠ 0:= by
      by_contra H
      replace H : x = -4:= by linarith
      trivial
    rw [show (x ^ 2 + x) / (x + 4) - 6 = ((x + 3) * (x - 8)) / (x + 4) by field_simp ; linarith] at h
    clear gx hx1 hx2
    replace hx : x < -4 ∨ x > -4:= by exact lt_or_gt_of_ne hx
    rcases hx with hx | hx
    .
      have g1 : x + 4 < 0:= by linarith
      have g2 : x + 3 < 0:= by linarith
      have g3 : x - 8 < 0:= by linarith
      replace g2 : (x + 3) * (x - 8) > 0:= by exact mul_pos_of_neg_of_neg g2 g3
      replace g2 : (x + 3) * (x - 8) / (x + 4) < 0:= by exact div_neg_of_pos_of_neg g2 g1
      linarith
    .
      by_cases hx1 : x < -3
      .
        simp
        left
        exact ⟨hx, hx1⟩
      .
        simp at hx1
        by_cases hx2 : x > 8
        .
          simp
          right
          exact hx2
        .
          simp at hx2
          have g1 : x - 8 ≤ 0:= by linarith
          have g2 : x + 3 ≥ 0:= by linarith
          have g3 : x + 4 > 0:= by linarith
          replace g2 : (x + 3) * (x - 8) ≤ 0:= by exact mul_nonpos_of_nonneg_of_nonpos g2 g1
          replace g2 : (x + 3) * (x - 8) / (x + 4) ≤ 0:= by
            rw [show (x + 3) * (x - 8) / (x + 4) = (x + 3) * (x - 8) * (1 / (x + 4)) by field_simp]
            replace g3 : 1 / (x + 4) ≥ 0:= by positivity
            exact mul_nonpos_of_nonpos_of_nonneg g2 g3
          linarith
  .
    intro h
    rcases h with (h | h)
    · -- Case x ∈ (-4, -3)
      rcases h with ⟨h1, h2⟩
      have h3 : x > -4 := h1
      have h4 : x < -3 := h2
      have hx3 : x + 4 > 0 := by
        linarith
      have h11 : (x ^ 2 + x) / (x + 4) > 6 := by
        have h5_1 : x + 4 > 0 := by linarith
        have h5_2 : x ^ 2 + x > 6 * (x + 4) := by
          nlinarith [sq_nonneg (x + 3)]
        have h5_3 : (x ^ 2 + x) / (x + 4) > 6 := by
          apply (lt_div_iff₀ h5_1).mpr
          linarith
        linarith
      have h7l : logb 6 ((x ^ 2 + x) / (x + 4)) > 1 := by
        have h5 : (x ^ 2 + x) / (x + 4) > 6 := h11
        have h6l : logb 6 ((x ^ 2 + x) / (x + 4)) > 1 := by
          have h4l : logb 6 ((x ^ 2 + x) / (x + 4)) = (log ((x ^ 2 + x) / (x + 4)) ) / (log (6 : ℝ)) := by
            field_simp [logb]
          rw [h4l]
          have h8l : log ((x ^ 2 + x) / (x + 4)) > log (6 : ℝ) := by
            apply Real.log_lt_log
            all_goals
            nlinarith
          have h9l : log (6 : ℝ) > 0 := by
            apply log_pos
            all_goals
            norm_num
          have h13l : (log ((x ^ 2 + x) / (x + 4)) ) / (log (6 : ℝ)) > (1 : ℝ) := by
            apply (lt_div_iff₀ h9l).mpr
            linarith
          linarith
        linarith
      have h9 : logb 0.3 (logb 6 ((x ^ 2 + x) / (x + 4))) < 0 := by
        have h11l : logb 6 ((x ^ 2 + x) / (x + 4)) > 1 := h7l
        rw [logb]
        have h14 : log (0.3 : ℝ) < 0 := by
          have h7 : (0.3 : ℝ) < 1 := by norm_num
          have h8 : (0.3 : ℝ) > 0 := by norm_num
          exact log_neg h8 h7
        have h18l : log (logb 6 ((x ^ 2 + x) / (x + 4))) > 0 := by
          have h17l : logb 6 ((x ^ 2 + x) / (x + 4)) > 1 := h7l
          have h19l : log (logb 6 ((x ^ 2 + x) / (x + 4))) > log (1 : ℝ) := by
            apply Real.log_lt_log
            all_goals
            nlinarith
          have h17l2 : log (1 : ℝ) = 0 := by
            simp
          linarith
        have h3l : log (logb 6 ((x ^ 2 + x) / (x + 4))) / log (0.3 : ℝ) < 0 := by
          apply div_neg_of_pos_of_neg
          all_goals
          try linarith
          all_goals
          try nlinarith
        linarith
      assumption
    · -- Case x ∈ (8, ∞)
      have h5 : x > 8 := h
      have hx3 : x + 4 > 0 := by
        linarith
      have h5a : (x ^ 2 + x) / (x + 4) > 6 := by
        have h5_1 : x + 4 > 0 := by linarith
        have h5_2 : x ^ 2 + x > 6 * (x + 4) := by
          nlinarith [sq_nonneg (x - 8)]
        have h5_3 : (x ^ 2 + x) / (x + 4) > 6 := by
          apply (lt_div_iff₀ h5_1).mpr
          linarith
        linarith
      have h7l : logb 6 ((x ^ 2 + x) / (x + 4)) > 1 := by
        have h5 : (x ^ 2 + x) / (x + 4) > 6 := h5a
        have h6l : logb 6 ((x ^ 2 + x) / (x + 4)) > 1 := by
          have h4l : logb 6 ((x ^ 2 + x) / (x + 4)) = (log ((x ^ 2 + x) / (x + 4)) ) / (log (6 : ℝ)) := by
            field_simp [logb]
          rw [h4l]
          have h8l : log ((x ^ 2 + x) / (x + 4)) > log (6 : ℝ) := by
            apply Real.log_lt_log
            all_goals
            nlinarith
          have h9l : log (6 : ℝ) > 0 := by
            apply log_pos
            all_goals
            norm_num
          have h13l : (log ((x ^ 2 + x) / (x + 4)) ) / (log (6 : ℝ)) > (1 : ℝ) := by
            apply (lt_div_iff₀ h9l).mpr
            linarith
          linarith
        linarith
      have h9 : logb 0.3 (logb 6 ((x ^ 2 + x) / (x + 4))) < 0 := by
        have h11l : logb 6 ((x ^ 2 + x) / (x + 4)) > 1 := h7l
        rw [logb]
        have h14 : log (0.3 : ℝ) < 0 := by
          have h7 : (0.3 : ℝ) < 1 := by norm_num
          have h8 : (0.3 : ℝ) > 0 := by norm_num
          exact log_neg h8 h7
        have h18l : log (logb 6 ((x ^ 2 + x) / (x + 4))) > 0 := by
          have h17l : logb 6 ((x ^ 2 + x) / (x + 4)) > 1 := h7l
          have h19l : log (logb 6 ((x ^ 2 + x) / (x + 4))) > log (1 : ℝ) := by
            apply Real.log_lt_log
            all_goals
            nlinarith
          have h17l2 : log (1 : ℝ) = 0 := by
            simp
          linarith
        have h3l : log (logb 6 ((x ^ 2 + x) / (x + 4))) / log (0.3 : ℝ) < 0 := by
          apply div_neg_of_pos_of_neg
          all_goals
          try linarith
          all_goals
          try nlinarith
        linarith
      assumption