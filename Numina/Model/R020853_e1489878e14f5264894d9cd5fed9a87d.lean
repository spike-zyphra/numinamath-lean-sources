import Mathlib

theorem algebra_22110 {x : ℝ} (hx : x > 0 ∧ x ≠ 1) : (7 : ℝ)^(Real.logb x 49) = 49 ↔ x = 7 := by
  constructor
  · -- Forward direction: if $7^{\log_x 49} = 49$, then $x = 7$
    intro h_eq
    have h1 : Real.logb x 49 = 2 := by
      have h2 : Real.logb 7 ((7 : ℝ) ^ (Real.logb x 49)) = Real.logb 7 (49 : ℝ) := by
        rw [h_eq]
      have h3 : Real.logb 7 ((7 : ℝ) ^ (Real.logb x 49)) = Real.logb x 49 := by
        rw [Real.logb_rpow]
        all_goals linarith
      have h4 : Real.logb 7 (49 : ℝ) = (2 : ℝ) := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h3] at h2
      rw [h4] at h2
      linarith
    -- From $\log_x 49 = 2$, we have $x^2 = 49$.
    have eq1 : x ^ 2 = (49 : ℝ) := by
      have h2_eq : x ^ (2 : ℝ) = (49 : ℝ) := by
        rw [Real.logb_eq_iff_rpow_eq] at h1
        · -- The main equality
          linarith
        all_goals
          rcases hx with ⟨hx_pos, hx_ne_one⟩
          all_goals
            try { linarith [hx_pos] }
            try { tauto }
            try { norm_num }
            try { linarith }
      norm_cast at h2_eq ⊢
      all_goals nlinarith
      <;> ring_nf
      <;> norm_num
    -- Solving the quadratic with the constraint that x is positive from hx.1. 
    have h3 : x = 7 := by 
      nlinarith [sq_pos_of_pos (show 0 < x by linarith [hx.1]), sq_nonneg (x - 7)]
    exact h3
  · -- Backward direction: if x = 7, then $7^{\log_x 49} = 49$
    intro h_eq
    rw [h_eq]
    have h1 : Real.logb (7 : ℝ) (49 : ℝ) = (2 : ℝ) := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h1]
    all_goals norm_num