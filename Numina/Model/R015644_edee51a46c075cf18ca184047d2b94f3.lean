import Mathlib

theorem algebra_179981 (x : ℝ) (hx : x > 0) :
    3^(Real.logb 3 x)^2 + x^(Real.logb 3 x) = 162 ↔ x = 1/9 ∨ x = 9 := by 
  constructor
  · -- First, we prove that if the equation holds, then x = 1/9 or x = 9 
    intro h_eq 
    have h1 : x ^ (Real.logb 3 x) = (3 : ℝ) ^ ((Real.logb 3 x) ^ 2) := by
      have h5_eq : x ^ (Real.logb 3 x) = ((3 : ℝ) ^ (Real.logb 3 x)) ^ (Real.logb 3 x) := by
        rw [show (3 : ℝ) ^ (Real.logb 3 x) = x by
          have h5 : (3 : ℝ) ^ (Real.logb 3 x) = x := by
            rw [Real.rpow_logb]
            all_goals
              try norm_num
              try linarith 
          linarith 
        ]
      rw [h5_eq]
      have h5_eq2 : ((3 : ℝ) ^ (Real.logb 3 x)) ^ (Real.logb 3 x) = (3 : ℝ) ^ ( (Real.logb 3 x) * (Real.logb 3 x) ) := by
        rw [← Real.rpow_mul]
        ring_nf 
        all_goals positivity 
      rw [h5_eq2]
      have h5_eq3 : (3 : ℝ) ^ ( (Real.logb 3 x) * (Real.logb 3 x) ) = (3 : ℝ) ^ ( (Real.logb 3 x) ^ 2 ) := by 
        ring_nf 
      rw [h5_eq3]
    have h_eq1 : (3 : ℝ) ^ (Real.logb 3 x) ^ 2 + (3 : ℝ) ^ (Real.logb 3 x) ^ 2 = 162 := by 
      linarith [ h_eq, h1 ]
    have h_eq2 : (3 : ℝ) ^ (Real.logb 3 x) ^ 2 = 81 := by 
      linarith 
    have h_eq3 : (Real.logb 3 x) ^ 2 = (4 : ℝ) := by
      have h_eq4 : (3 : ℝ) ^ ( (Real.logb 3 x) ^ 2 ) = (3 : ℝ) ^ ( (4 : ℝ) ) := by 
        rw [ h_eq2 ]
        norm_num 
      have h_eq5 : (Real.logb 3 x) ^ 2 = (4 : ℝ) := by
        apply_fun (Real.logb 3) at h_eq4 
        have h1' : Real.logb 3 ( (3 : ℝ) ^ ( (Real.logb 3 x) ^ 2 ) ) = (Real.logb 3 x) ^ 2 := by
          rw [Real.logb_rpow]
          all_goals
            try norm_num
            try linarith 
        have h2' : Real.logb 3 ( (3 : ℝ) ^ ( (4 : ℝ) ) ) = (4 : ℝ) := by 
          rw [Real.logb_rpow]
          all_goals
            try norm_num
            try linarith 
        linarith [ h_eq4, h1', h2' ]
      linarith 
    have h_eq41 : Real.logb 3 x = 2 ∨ Real.logb 3 x = -2 := by 
      have h_eq52 : (Real.logb 3 x) ^ 2 = (4 : ℝ) := h_eq3
      have h_eq62 : (Real.logb 3 x - 2) * (Real.logb 3 x + 2) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.1 h_eq62) with h_eq72 h_eq82 
      · -- Real.logb 3 x - 2 = 0 
        left 
        linarith 
      · -- Real.logb 3 x + 2 = 0 
        right 
        linarith 
    cases h_eq41 with
    | inl h_eq51 =>
      right
      have h_eq61 : x = (3 : ℝ) ^ ((2 : ℝ) ) := by 
        rw [ Real.logb_eq_iff_rpow_eq ] at h_eq51 
        · linarith 
        all_goals 
          try norm_num 
          try linarith 
      norm_num at h_eq61 ⊢ 
      all_goals linarith 
    | inr h_eq52 =>
      left 
      have h_eq71 : x = (3 : ℝ) ^ ( (-2 : ℝ) ) := by 
        rw [ Real.logb_eq_iff_rpow_eq ] at h_eq52 
        · linarith 
        all_goals 
          try norm_num 
          try linarith 
      norm_num at h_eq71 ⊢ 
      all_goals linarith 
  · -- Assume x = 1/9 or x = 9, prove the equation 
    rintro (h_eq | h_eq)
    · -- x = 1/9 
      rw [h_eq]
      have h1 : Real.logb 3 ( (1 / 9 : ℝ) ) = -2 := by 
        rw [ Real.logb_eq_iff_rpow_eq ] <;> norm_num 
      rw [h1] 
      norm_num
    · -- x = 9 
      rw [h_eq]
      have h1 : Real.logb 3 ( (9 : ℝ) ) = 2 := by 
        rw [ Real.logb_eq_iff_rpow_eq ] <;> norm_num 
      rw [h1]
      norm_num