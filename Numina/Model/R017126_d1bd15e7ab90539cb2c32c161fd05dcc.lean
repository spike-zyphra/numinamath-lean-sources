import Mathlib

open Real

theorem algebra_158467 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : (x ^ 2 * y ^ 4) ^ (-log x) = y ^ log (y / x ^ 7)) (h2 : y ^ 2 - x * y - 2 * x ^ 2 + 8 * x - 4 * y = 0) :
    (x = 2 ∧ y = 2) ∨ (x = 2 ∧ y = 4) ∨ (x = (Real.sqrt 17 - 1) / 2 ∧ y = (9 - Real.sqrt 17) / 2) := by
  have h3 : log ((x ^ 2 * y ^ 4) ^ (-log x)) = (-log x) * log (x ^ 2 * y ^ 4) := by
    rw [log_rpow]
    all_goals
      have h4_pos : 0 < x ^ 2 * y ^ 4 := by
        positivity
      nlinarith [show x ^ 2 * y ^ 4 > 0 by positivity]
  have h5 : log (x ^ 2 * y ^ 4) = 2 * log x + 4 * log y := by
    have h6 : log (x ^ 2 * y ^ 4) = log (x ^ 2) + log (y ^ 4) := by 
      rw [log_mul (by positivity) (by positivity)]
    have h7 : log (x ^ 2) = 2 * log x := by 
      simp [log_pow]
    have h8 : log (y ^ 4) = 4 * log y := by 
      simp [log_pow]
    linarith [h6, h7, h8]
  have h4 : log (y ^ log (y / x ^ 7)) = (log (y / x ^ 7)) * log y := by 
    rw [log_rpow]
    all_goals linarith
  have h7 : log (y / x ^ 7) = log y - 7 * log x := by 
    have h8 : log (y / x ^ 7) = log y - log (x ^ 7) := by
      rw [log_div (by positivity) (by positivity)]
    have h9 : log (x ^ 7) = 7 * log x := by 
      simp [log_pow]
    linarith [h8, h9]
  have eq1 : log ((x ^ 2 * y ^ 4) ^ (-log x)) = log (y ^ log (y / x ^ 7)) := by 
    rw [h1]
  have eq2 : (-log x) * (2 * log x + 4 * log y) = (log y - 7 * log x) * log y := by
    have eq3 : log ((x ^ 2 * y ^ 4) ^ (-log x)) = log (y ^ log (y / x ^ 7)) := by 
      rw [h1]
    rw [h3, h5] at eq3
    rw [h4, h7] at eq3
    linarith [eq3]
  have h_eq5 : (2 * (log x) - (log y)) * ((log x) - (log y)) = 0 := by 
    nlinarith [eq2]
  cases' (mul_eq_zero.mp h_eq5) with h_eq6 h_eq7
  · -- Case $2 \ln x = \ln y$
    have h_eq4 : log y = 2 * (log x) := by 
      linarith
    have eq3 : y = x ^ 2 := by
      have h_eq5 : log y = 2 * (log x) := h_eq4
      have h_eq6 : log y = log (x ^ 2) := by
        have : log (x ^ 2) = 2 * (log x) := by
          simp [log_pow]
        linarith [this, h_eq5]
      have h_eq7 : y > 0 := by linarith
      have h_eq8 : x ^ 2 > 0 := by positivity
      have h_eq9 : y = x ^ 2 := by 
        apply log_injOn_pos (Set.mem_Ioi.mpr (by linarith : y > 0)) (Set.mem_Ioi.mpr (by positivity : x ^ 2 > 0)) (by
          linarith [h_eq6]
        )
        all_goals linarith
      linarith [h_eq7, h_eq8, h_eq9]
    rw [show y = x ^ 2 by linarith [eq3]] at h2
    have h8 : (x - 2) * (x ^ 2 + x - 4) = 0 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 2), sq_pos_of_pos (show x > 0 by linarith)]
    cases' (mul_eq_zero.mp h8) with h9 h10
    · -- Case x = 2
      have hx2 : x = 2 := by linarith
      have hy4 : y = 4 := by 
        nlinarith [show y = x ^ 2 by linarith [eq3], hx2]
      right
      left
      exact ⟨hx2, hy4⟩
    · -- Case x^2 + x - 4 = 0
      have h_eq5 : x ^ 2 + x - 4 = 0 := by
        nlinarith
      have h_eq6 : x = (Real.sqrt 17 - 1) / 2 := by 
        have h10 : (x - ( (Real.sqrt 17 - 1) / 2 )) * (x - ( (-1 - Real.sqrt 17) / 2 )) = 0 := by
          nlinarith [h_eq5, Real.sqrt_pos.mpr (show (0 : ℝ) < (17 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
        cases' (mul_eq_zero.mp h10) with h11 h12
        · -- x - (Real.sqrt 17 - 1)/2 = 0
          linarith
        · -- Contradicts x > 0
          nlinarith [h12, Real.sqrt_pos.mpr (show (0 : ℝ) < (17 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
      have hy_eq : y = (9 - Real.sqrt 17) / 2 := by
        have h7 : y = x^2 := by linarith [eq3]
        rw [h7]
        rw [show x = (Real.sqrt 17 - 1) / 2 by linarith [h_eq6]]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (17 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
      right
      right
      exact ⟨by linarith, by linarith⟩
  · -- Case $ \ln x = \ln y$
    have h_eq8 : log x = log y := by linarith
    have eq3 : x = y := by
      have h_eq5 : log x = log y := h_eq8
      have h_eq7 : x > 0 := by linarith
      have h_eq8 : y > 0 := by linarith
      have h_eq9 : x = y := by
        apply log_injOn_pos (Set.mem_Ioi.mpr (by linarith : x > 0)) (Set.mem_Ioi.mpr (by linarith : y > 0)) (by
          linarith [h_eq5]
        )
        all_goals linarith
      linarith [h_eq7, h_eq8, h_eq9]
    have h20 : x ^ 2 - x * x - 2 * x ^ 2 + 8 * x - 4 * x = 0 := by
      have h16 : x = y := by
        linarith [eq3]
      rw [show y = x by linarith [h16]] at h2
      linarith
    have h24 : x = 2 := by
      nlinarith [sq_pos_of_pos (show x > 0 by linarith)]
    have hy2 : y = 2 := by 
      nlinarith [eq3, h24]
    left
    exact ⟨h24, hy2⟩