import Mathlib

theorem algebra_289277 (a : ℝ) : 5^a + 5^(a + 1) = Real.sqrt 4500 ↔ a = 3 / 2 := by
  constructor
  · -- Assume 5^a + 5^(a + 1) = √4500, prove a = 3/2
    intro h
    have h1 : (5 : ℝ) ^ a + (5 : ℝ) ^ (a + 1) = 6 * ((5 : ℝ) ^ a) := by
      rw [show a + 1 = a + (1 : ℝ) by ring]
      rw [Real.rpow_add]
      ring_nf
      all_goals norm_num
    rw [h1] at h

    have h2 : Real.sqrt 4500 = 30 * Real.sqrt 5 := by
      calc
        Real.sqrt 4500 = Real.sqrt (30^2 * 5) := by norm_num
        _ = (30 : ℝ) * Real.sqrt 5 := by
          rw [Real.sqrt_mul (by norm_num)]
          rw [Real.sqrt_sq (by norm_num)]
    rw [h2] at h

    -- From 6 * 5^a = 30 * sqrt(5), we get 5^a = 5 * sqrt(5)
    have h3 : (5 : ℝ) ^ a = 5 * Real.sqrt 5 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 4500, Real.rpow_pos_of_pos (show 0 < (5 : ℝ) by norm_num) a, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]

    -- Let's prove that 5 * sqrt(5) = 5^(3/2)
    have h4 : (5 : ℝ) ^ a = (5 : ℝ) ^ (3 / 2 : ℝ) := by
      have h5 : (5 : ℝ) ^ (3 / 2 : ℝ) = 5 * Real.sqrt 5 := by
        have h51 : (5 : ℝ) ^ (3 / 2 : ℝ) = ((5 : ℝ) ^ (1 : ℝ)) * ((5 : ℝ) ^ (1 / 2 : ℝ)) := by 
          rw [← Real.rpow_add]
          norm_num
          all_goals norm_num
        rw [h51]
        have h52 : (5 : ℝ) ^ (1 : ℝ) = (5 : ℝ) := by
          simp
        have h53 : (5 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 5 := by
          rw [Real.sqrt_eq_rpow]
        rw [h52, h53]
        all_goals nlinarith
      rw [h5] at *
      all_goals linarith [h3, h5]

    -- Now using injectivness of exponentiation we get a = 3/2
    have h6 : a = (3 / 2 : ℝ) := by 
      apply_fun (Real.logb (5 : ℝ)) at h4
      have h7 : Real.logb (5 : ℝ) ((5 : ℝ) ^ a) = Real.logb (5 : ℝ) ((5 : ℝ) ^ (3 / 2 : ℝ)) := by 
        linarith [h4]
      have h8 : Real.logb (5 : ℝ) ((5 : ℝ) ^ a) = a := by 
        rw [Real.logb_rpow]
        all_goals norm_num
      have h9 : Real.logb (5 : ℝ) ((5 : ℝ) ^ (3 / 2 : ℝ)) = (3 / 2 : ℝ) := by 
        rw [Real.logb_rpow]
        all_goals norm_num
      linarith [h7, h8, h9]
    linarith
  · -- Assume a = 3/2, prove 5^a + 5^(a + 1) = √4500
    intro h
    rw [show a = (3 / 2 : ℝ) by linarith [h]]
    have h1 : (5 : ℝ) ^ (3 / 2 : ℝ) + (5 : ℝ) ^ (3 / 2 + 1 : ℝ) = 6 * ((5 : ℝ) ^ (3 / 2 : ℝ)) := by 
      have h11 : (5 : ℝ) ^ (3 / 2 + 1 : ℝ) = (5 : ℝ) ^ (3 / 2 : ℝ) * (5 : ℝ) ^ (1 : ℝ) := by 
        rw [← Real.rpow_add]
        ring_nf
        all_goals norm_num
      rw [h11]
      norm_num
      <;> ring_nf 
    have h2 : 6 * ((5 : ℝ) ^ (3 / 2 : ℝ)) = Real.sqrt 4500 := by
      have h61 : (5 : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt 125 := by
        have h62 : (5 : ℝ) ^ (3 / 2 : ℝ) = ((5 : ℝ) ^ (3 : ℝ)) ^ (1 / 2 : ℝ) := by 
          rw [← Real.rpow_mul]
          ring_nf
          all_goals norm_num
        rw [h62]
        have h63 : (5 : ℝ) ^ (3 : ℝ) = (125 : ℝ) := by 
          norm_num
        rw [h63]
        have h64 : ((125 : ℝ) : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 125 := by
          rw [Real.sqrt_eq_rpow]
        rw [h64]
      have h31 : Real.sqrt 125 = (5 * Real.sqrt 5) := by
        have h31a : Real.sqrt 125 = Real.sqrt (5 ^ 2 * 5) := by norm_num
        rw [h31a]
        have h31b : Real.sqrt ( (5 ^ 2 : ℝ) * (5 : ℝ) ) = (5 : ℝ) * Real.sqrt (5 : ℝ) := by
          rw [Real.sqrt_mul (by norm_num)]
          rw [Real.sqrt_sq (by norm_num)]
        rw [h31b]
      have h71 : Real.sqrt (4500 : ℝ) = 30 * Real.sqrt 5 := by
        calc
          Real.sqrt (4500 : ℝ) = Real.sqrt (30 ^ 2 * 5) := by norm_num
          _ = (30 : ℝ) * Real.sqrt (5 : ℝ) := by
            rw [Real.sqrt_mul (by norm_num)]
            rw [Real.sqrt_sq (by norm_num)]
      rw [h61, h31, h71]
      all_goals nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 4500, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (4500 : ℝ) by norm_num)]
    linarith [h1, h2]