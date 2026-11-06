import Mathlib

set_option maxRecDepth 5000


theorem algebra_149071 (x : ℝ) (hx : x > 0) :
    (3 * x / 2) ^ Real.logb 3 (8 * x) = x ^ 7 / 8 ↔
    x = 729 / 8 ∨ x = 2 := by
  constructor
  · -- Assume the equation $(3 * x / 2) ^ \log_3 (8 * x) = x ^ 7 / 8$, prove $x = 729 / 8 ∨ x = 2$
    intro h
    have h1 : Real.logb 3 ((3 * x / 2) ^ Real.logb 3 (8 * x)) = Real.logb 3 (x ^ 7 / 8) := by
      rw [h]
    have h2 : Real.logb 3 ((3 * x / 2) ^ Real.logb 3 (8 * x)) = Real.logb 3 (8 * x) * Real.logb 3 (3 * x / 2) := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      positivity
    have h4 : Real.logb 3 (x ^ 7 / 8) = Real.logb 3 (x ^ 7) - Real.logb 3 (8) := by
      have h1 : (x ^ 7 : ℝ) > 0 := by positivity
      have h2 : (8 : ℝ) > 0 := by norm_num
      exact Real.logb_div (by positivity) (by positivity)
    have h41 : Real.logb 3 (x ^ 7) = 7 * Real.logb 3 x := by
      simp [Real.logb_pow]
    have h6 : Real.logb 3 (8) = 3 * Real.logb 3 (2) := by
      calc
        Real.logb 3 (8) = Real.logb 3 (2 ^ 3) := by norm_num
        _ = 3 * Real.logb 3 (2) := by simp [Real.logb_pow]
    rw [h2] at h1
    rw [h4] at h1
    rw [h41] at h1
    rw [h6] at h1
    have h7 : Real.logb 3 (3 * x / 2) = Real.logb 3 (3 * x) - Real.logb 3 (2) := by
      have h1 : (3 * x : ℝ) > 0 := by positivity
      have h2 : (2 : ℝ) > 0 := by norm_num
      have h3 : (3 * x / 2 : ℝ) = (3 * x) / (2) := by ring
      rw [h3]
      field_simp [Real.logb_div]
    have h8 : Real.logb 3 (3 * x) = Real.logb 3 3 + Real.logb 3 x := by
      have h1 : (3 : ℝ) > 0 := by norm_num
      have h2 : (x : ℝ) > 0 := by linarith
      exact Real.logb_mul (by linarith) (by linarith)
    have h8' : Real.logb 3 (3 : ℝ) = 1 := by
      rw [Real.logb_self_eq_one]
      all_goals linarith
    rw [h7, h8, h8'] at h1
    have h5 : Real.logb 3 (8 * x) = Real.logb 3 8 + Real.logb 3 x := by
      have h1 : (8 : ℝ) > 0 := by norm_num
      have h2 : (x : ℝ) > 0 := by linarith
      exact Real.logb_mul (by linarith) (by linarith)
    rw [h5] at h1
    have h9 : Real.logb 3 (8) = 3 * Real.logb 3 (2) := by
      calc
        Real.logb 3 (8) = Real.logb 3 (2 ^ 3) := by norm_num
        _ = 3 * Real.logb 3 (2) := by simp [Real.logb_pow]
    rw [h9] at h1
    have h10 : (Real.logb 3 x - Real.logb 3 (2 : ℝ)) * (Real.logb 3 x - (6 - 3 * Real.logb 3 (2 : ℝ)) ) = 0 := by
      nlinarith [sq_nonneg (Real.logb 3 x - Real.logb 3 (2 : ℝ)), sq_nonneg (Real.logb 3 (2 : ℝ) * 3 - 3), sq_nonneg (Real.logb 3 x), sq_nonneg (Real.logb 3 (2 : ℝ) - 1)]
    cases (mul_eq_zero.mp h10) with
    | inl h_eq1 =>
      have h11 : Real.logb 3 x = Real.logb 3 (2 : ℝ) := by
        linarith
      have h12 : x = 2 := by
        have h34 : x = (2 : ℝ) := by
          apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr (show (2 : ℝ) > 0 by norm_num)) h11
        norm_num at h34 ⊢
        <;> linarith
      right
      simp [h12]
    | inr h_eq2 =>
      have h13 : Real.logb 3 x = 6 - 3 * Real.logb 3 (2 : ℝ) := by
        linarith
      have h14 : x = (729 / 8 : ℝ) := by
        have h34 : x = (3 : ℝ) ^ (Real.logb 3 x : ℝ) := by
          field_simp
        rw [h34, h13]
        have h35 : (3 : ℝ) ^ (6 - 3 * Real.logb 3 (2 : ℝ) : ℝ) = (729 / 8 : ℝ) := by
          have h37 : (3 : ℝ) ^ (6 - 3 * Real.logb 3 (2 : ℝ) : ℝ) = (3 : ℝ) ^ (6 : ℝ) / (3 : ℝ) ^ (3 * Real.logb 3 (2 : ℝ) : ℝ) := by
            rw [← Real.rpow_sub]
            ring_nf
            all_goals linarith
          rw [h37]
          have h38 : (3 : ℝ) ^ (6 : ℝ) = (729 : ℝ) := by norm_num
          have h39 : (3 : ℝ) ^ (3 * Real.logb 3 (2 : ℝ) : ℝ) = (8 : ℝ) := by
            have h40 : (3 : ℝ) ^ (3 * Real.logb 3 (2 : ℝ) : ℝ) = ((3 : ℝ) ^ (Real.logb 3 (2 : ℝ) : ℝ)) ^ (3 : ℝ) := by
              rw [← Real.rpow_mul]
              ring_nf
              all_goals linarith
            rw [h40]
            have h41 : (3 : ℝ) ^ (Real.logb 3 (2 : ℝ) : ℝ) = (2 : ℝ) := by
              rw [Real.rpow_logb]
              all_goals linarith
            rw [h41]
            all_goals norm_num
          rw [h38, h39]
        linarith
      left
      simp [h14]
  · -- Assume $x = 729 / 8 ∨ x = 2$, prove $(3 * x / 2) ^ \log_3 (8 * x) = x ^ 7 / 8$
    rintro (h | h)
    · -- Case $x = 729 / 8$
      rw [h]
      have h529 : Real.logb (3 : ℝ) (8 * (729 / 8 : ℝ)) = (6 : ℝ) := by
        have h654 : (8 * (729 / 8 : ℝ) : ℝ) = (729 : ℝ) := by ring
        rw [h654]
        have h63813 : (729 : ℝ) = (3 : ℝ) ^ (6 : ℝ) := by norm_num
        rw [h63813]
        rw [Real.logb_rpow]
        all_goals norm_num
      have h577 : (3 * (729 / 8 : ℝ) / 2 : ℝ) = (2187 / 16 : ℝ) := by norm_num
      have h7398eq : ((3 * (729 / 8 : ℝ) / 2 : ℝ) : ℝ) ^ (6 : ℝ) = ((729 / 8 : ℝ) ^ 7 / (8 : ℝ)) := by
        rw [h577]
        norm_num
      rw [h529]
      rw [h7398eq]
    · -- Case $x = 2$
      rw [h]
      have h529 : Real.logb (3 : ℝ) (8 * (2 : ℝ)) = 4 * Real.logb 3 (2 : ℝ) := by
        have h55 : (8 * (2 : ℝ) : ℝ) = (16 : ℝ) := by norm_num
        rw [h55]
        have h57 : Real.logb (3 : ℝ) (16 : ℝ) = 4 * Real.logb 3 (2 : ℝ) := by
          calc
            Real.logb (3 : ℝ) (16 : ℝ) = Real.logb (3 : ℝ) ((2 : ℝ) ^ 4) := by norm_num
            _ = 4 * Real.logb (3 : ℝ) (2 : ℝ) := by simp [Real.logb_pow]
        linarith [h57]
      have h577 : (3 * (2 : ℝ) / 2 : ℝ) = (3 : ℝ) := by ring_nf
      have h7398eq : ((3 * (2 : ℝ) / 2 : ℝ) : ℝ) ^ (4 * Real.logb 3 (2 : ℝ) : ℝ) = ((2 : ℝ) ^ 7 / (8 : ℝ)) := by
        rw [h577]
        have h41 : (3 : ℝ) ^ (4 * Real.logb 3 (2 : ℝ) : ℝ) = (2 ^ 4 : ℝ) := by
          have h42 : (3 : ℝ) ^ (4 * Real.logb 3 (2 : ℝ) : ℝ) = ((3 : ℝ) ^ (Real.logb 3 (2 : ℝ) : ℝ)) ^ (4 : ℝ) := by
            rw [← Real.rpow_mul]
            ring_nf
            all_goals linarith
          have h433101 : (3 : ℝ) ^ (Real.logb 3 (2 : ℝ) : ℝ) = (2 : ℝ) := by
            rw [Real.rpow_logb]
            all_goals linarith
          rw [h42, h433101]
          all_goals norm_num
        have h5014 : ((2 : ℝ) ^ 7 / (8 : ℝ)) = (2 ^ 4 : ℝ) := by
          norm_num
        rw [h41]
        all_goals linarith [h5014]
      rw [h529]
      rw [h7398eq]