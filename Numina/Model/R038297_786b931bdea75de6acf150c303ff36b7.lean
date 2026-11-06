import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_131961 {α b : ℝ} (h₀ : α ∈ Ioo 0 (π/4)) (h₁ : b ∈ Ioo 0 1) :
    ((sin α)^(logb b (sin α)) < (sin α)^(logb b (cos α))) ∧
    ((sin α)^(logb b (cos α)) < (cos α)^(logb b (cos α))) := by
  rcases h₀ with ⟨hα1, hα2⟩
  rcases h₁ with ⟨hb1, hb2⟩
  have h2 : 0 < sin α := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [hα1, Real.pi_pos]
    linarith [hα2, Real.pi_pos]
  have h3 : 0 < cos α := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [hα1, hα2, Real.pi_pos]
  have h4 : sin α < cos α := by
    have hα3 : α < π / 4 := hα2
    have h5 : sin α < sin (π / 4) := by
      apply sin_lt_sin_of_lt_of_le_pi_div_two
      all_goals linarith [Real.pi_pos, hα3]
    have h6 : sin (π / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    have h7 : cos α > Real.sqrt 2 / 2 := by
      have hα8 : α < π / 4 := hα2
      have h9 : cos α > cos (π / 4) := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals linarith [Real.pi_pos, hα8]
      have h10 : cos (π / 4) = Real.sqrt 2 / 2 := by
        rw [cos_pi_div_four]
      linarith [h9, h10]
    nlinarith [h5, h6, h7]
  -- $\log_b \sin \alpha > \log_b \cos \alpha$ since $\sin \alpha < \cos \alpha$ and $\log_b$ is strictly decreasing.
  have h5 : logb b (sin α) > logb b (cos α) := by
    -- Since $0 < b < 1$, we have that $\log_b$ is strictly *decreasing*.
    apply Real.logb_lt_logb_of_base_lt_one
    all_goals nlinarith [h2, h3, h4, Real.sin_sq_add_cos_sq α]
  -- First part of the conjunction: $(\sin \alpha)^{\log_b \sin \alpha} < (\sin \alpha)^{\log_b \cos \alpha}$
  have h7 : (sin α) ^ (logb b (sin α)) < (sin α) ^ (logb b (cos α)) := by
    -- 0 < sin α < 1
    have h8 : sin α < 1 := by
      have hα8 : α < π / 4 := hα2
      have h9 : sin α < sin (π / 4) := by
        apply sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals linarith [Real.pi_pos, hα8]
      have h10 : sin (π / 4) = Real.sqrt 2 / 2 := by
        rw [sin_pi_div_four]
      have h11 : Real.sqrt 2 / 2 < 1 := by
        nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 2 by linarith), Real.sq_sqrt (show (0:ℝ) ≤ 2 by linarith)]
      nlinarith [h9, h10, h11]
    -- $\log_b \sin \alpha > \logb \cos \alpha$ 
    -- Since $0 < \sin \alpha < 1$, $t \mapsto (\sin \alpha)^t$ is strictly decreasing.
    have h8' : (sin α : ℝ) ^ (logb b (sin α)) < (sin α : ℝ) ^ (logb b (cos α)) := by
      apply Real.rpow_lt_rpow_of_exponent_gt
      all_goals nlinarith [h8, h2, h5]
    linarith
  -- Second part of the conjunction: $(\sin \alpha)^{\log_b \cos \alpha} < (\cos \alpha)^{\log_b \cos \alpha}$
  have h8 : (sin α) ^ (logb b (cos α)) < (cos α) ^ (logb b (cos α)) := by
    -- This time it's different.
    -- We need to show $0 < \logb \cos \alpha$.
    have h11 : 0 < cos α := h3
    have h13 : 0 < logb b (cos α) := by
      -- Now we need to show $\logb \cos \alpha > 0$
      -- Since $0 < b < 1$ and $\log_b$ is strictly decreasing and $\cos \alpha < 1$.
      have h14 : logb b (cos α) > logb b 1 := by
        apply Real.logb_lt_logb_of_base_lt_one
        all_goals nlinarith [h3, Real.sin_sq_add_cos_sq α, h2, h4, Real.sin_sq_add_cos_sq α]
      have h15 : logb b 1 = 0 := by
        rw [logb_one]
      nlinarith [h14, h15]
    -- using the fact that `t → t ^ x` is strict increasing when x > 0
    have h17 : sin α < cos α := h4
    have h18 : (sin α) ^ (logb b (cos α) ) < (cos α) ^ (logb b (cos α) ) := by
      apply Real.rpow_lt_rpow
      all_goals nlinarith [h11, h13, Real.sin_sq_add_cos_sq α, h17, Real.sin_sq_add_cos_sq α]
    linarith
  constructor
  · exact h7
  · exact h8