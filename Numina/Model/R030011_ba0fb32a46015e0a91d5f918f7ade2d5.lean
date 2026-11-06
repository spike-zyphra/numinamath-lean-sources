import Mathlib

theorem algebra_131844 {x : ℝ} (hx : x > 0) (h : Real.logb (x^2019) 2018 = 2018 / 2019) :
    x = 2018 ^ ((1 : ℝ) / 2018) := by
  have h1 : Real.logb (x ^ 2019) 2018 = (Real.log (2018 : ℝ) ) / (Real.log (x ^ 2019) ) := by 
    field_simp [Real.logb]
  rw [h1] at h
  have h2 : Real.log (x ^ 2019) = (2019 : ℝ) * Real.log x := by
    have h2019 : Real.log (x ^ 2019) = (2019 : ℝ) * Real.log x := by
      have h3 : Real.log (x ^ 2019) = (2019 : ℝ) * Real.log x := by
        rw [show (x ^ 2019 : ℝ) = (x) ^ (2019 : ℕ) by norm_num]
        simp [Real.log_pow]
        <;> nlinarith
      linarith
    linarith
  rw [h2] at h
  have h3 : Real.log (2018 : ℝ) = 2018 * Real.log x := by
    field_simp [(show Real.log x ≠ 0 by
      by_contra h4
      have h5 : Real.log x = 0 := by linarith [h4]
      have h6 : x = 1 := by
        rw [Real.log_eq_zero] at h5
        rcases h5 with (r | r | r)
        · linarith
        · linarith
        · linarith
      rw [h6] at h
      norm_num at h 
    )] at h ⊢
    linarith
  have h4 : Real.log x = (Real.log (2018 : ℝ) ) / (2018 : ℝ) := by 
    linarith
  have h5 : x = Real.exp (Real.log x) := by 
    rw [Real.exp_log]
    all_goals linarith
  rw [h4] at h5
  have h6 : Real.exp ( (Real.log (2018 : ℝ) ) / (2018 : ℝ) ) = (2018 : ℝ) ^ ((1 : ℝ) / 2018) := by 
    have h7 : Real.exp ( (Real.log (2018 : ℝ) ) / (2018 : ℝ) ) = Real.exp ( ( (1 / (2018 : ℝ) ) * (Real.log (2018 : ℝ) ) ) ) := by 
      ring_nf 
    rw [h7] 
    have h11 : Real.exp ( ( (1 / (2018 : ℝ) ) * (Real.log (2018 : ℝ) ) ) ) = (2018 : ℝ) ^ ((1 : ℝ) / 2018) := by 
      have h12 : Real.exp ( ( (1 / (2018 : ℝ) ) * (Real.log (2018 : ℝ) ) ) ) = (2018 : ℝ) ^ ((1 : ℝ) / 2018) := by
        have h13 : ( (2018 : ℝ) ^ ((1 : ℝ) / 2018) ) = Real.exp ( ( ( (1 : ℝ) / 2018 ) * Real.log (2018 : ℝ) ) ) := by
          rw [Real.rpow_def_of_pos (show (2018 : ℝ) > (0 : ℝ) by norm_num)]
          <;> ring_nf
        rw [h13]
        all_goals ring_nf
      linarith [h12]
    linarith [h11]
  linarith [h5, h6]