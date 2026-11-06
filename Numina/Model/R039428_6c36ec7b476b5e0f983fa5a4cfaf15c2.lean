import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_17007 :
  {b : ℝ | b > 0 ∧ b ≠ 1 ∧ ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ √(x * y) = b ^ b ∧ logb b (x ^ logb b y) + logb b (y ^ logb b x) = 4 * b ^ 4} = Ioc 0 (1 / √2) := by
  ext b
  simp only [Set.mem_setOf_eq, Set.mem_Ioc]
  constructor
  · -- First, let's prove the forward direction.
    rintro ⟨hb_pos, hb_ne_1, x, y, hx_pos, hy_pos, heq1, heq2⟩
    have h1 : x * y > 0 := mul_pos hx_pos hy_pos
    have heq1' : x * y = (b ^ b) ^ 2 := by
      calc
        x * y = (√(x * y)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = (b ^ b) ^ 2 := by rw [heq1]
    have h2 : logb b (x ^ logb b y) = (logb b y) * (logb b x) := by 
      have h21 : logb b (x ^ logb b y) = (logb b y) * (logb b x) := by
        rw [logb_rpow_eq_mul_logb_of_pos]
        all_goals linarith 
      linarith
    have h3 : logb b (y ^ logb b x) = (logb b x) * (logb b y) := by 
      have h31 : logb b (y ^ logb b x) = (logb b x) * (logb b y) := by
        rw [logb_rpow_eq_mul_logb_of_pos]
        all_goals linarith 
      linarith 
    have heq2' : (logb b y) * (logb b x) + (logb b x) * (logb b y) = 4 * b ^ 4 := by 
      rw [h2, h3] at heq2 
      linarith 
    have heq2'' : (logb b x) * (logb b y) = 2 * b ^ 4 := by 
      nlinarith
    have h4 : (logb b x) + (logb b y) = 2 * b := by
      have h5 : (logb b x) + (logb b y) = logb b (x * y) := by 
        rw [← logb_mul (by linarith) (by linarith)]
      have h6 : logb b (x * y) = 2 * b := by
        rw [show x * y = (b ^ b) ^ 2 by linarith [heq1']]
        have h7 : logb b ((b ^ b) ^ 2) = 2 * logb b (b ^ b) := by 
          simp [logb_pow]
        have h9 : logb b (b ^ b) = b := by 
          rw [logb_rpow]
          all_goals 
            try linarith 
            all_goals try 
              tauto 
        rw [h7, h9]
        <;> linarith 
      linarith [h5, h6]
    have h11 : (4 * b ^ 2) - (8 * b ^ 4) ≥ 0 := by 
      nlinarith [sq_nonneg (logb b x - logb b y), sq_nonneg ((logb b x) - b), sq_nonneg ((logb b y) - b), sq_nonneg (logb b x - logb b y), sq_nonneg (b^2 - 1/2)]
    have h12 : b^2 ≤ (1 / 2 : ℝ) := by nlinarith 
    have h13 : b ≤ (1 / Real.sqrt 2 : ℝ) := by
      have h14 : b ^ 2 ≤ (1 / 2 : ℝ) := h12
      have h11 : b > 0 := hb_pos
      have h3 : b ≤ Real.sqrt (1 / 2 : ℝ) := by 
        nlinarith [Real.sqrt_nonneg (1 / 2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num)]
      have h4 : Real.sqrt (1 / 2 : ℝ) = 1 / Real.sqrt 2 := by
        field_simp [Real.sqrt_eq_iff_sq_eq]
      linarith [h4, h3]
    constructor 
    · -- Show $0 < b$
      linarith 
    · -- Show $b \le 1 / \sqrt 2$
      linarith 
  · -- Assume b in (0,1/√2], need to prove left side
    rintro ⟨hb_pos, hb_le⟩
    have hb_ne_1 : b ≠ 1 := by 
      by_contra h
      have h1 : b = 1 := by nlinarith 
      have h2 : b ≤ 1 / Real.sqrt 2 := hb_le 
      rw [h1] at h2 
      have h3 : (1 / Real.sqrt 2 : ℝ) < (1 : ℝ) := by 
        have h4 : Real.sqrt 2 > 1 := by 
          nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        have h5 : (1 / Real.sqrt 2 : ℝ) < (1 : ℝ) := by 
          apply (div_lt_iff₀ (by positivity)).mpr 
          nlinarith 
        linarith 
      linarith [h2, h3, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    constructor 
    · exact hb_pos 
    constructor 
    · exact_mod_cast hb_ne_1
    have h12 : b ^ 2 ≤ (1 / 2 : ℝ) := by 
      have h13 : b ≤ (1 / Real.sqrt 2 : ℝ) := hb_le 
      have h15 : b ^ 2 ≤ (1 / Real.sqrt 2 : ℝ) ^ 2 := by 
        nlinarith [h13, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
      have h16 : (1 / Real.sqrt 2 : ℝ) ^ 2 = (1 / 2 : ℝ) := by 
        field_simp [Real.sq_sqrt] 
      nlinarith [h15, h16] 
    have h14 : ∃ s : ℝ, s ≥ 0 ∧ s^2 = b^2 - 2 * b^4 := by
      use Real.sqrt (b^2 - 2 * b^4)
      constructor 
      · -- Show that sqrt of nonneg value is >=0.
        apply Real.sqrt_nonneg 
      · -- Show that (sqrt y)^2 = y for y >=0.
        have h5' : b^2 - 2 * b^4 ≥ 0 := by 
          nlinarith 
        rw [Real.sq_sqrt] 
        linarith 
    rcases h14 with ⟨s, hs_nonneg, h_s_sq⟩
    use (b ^ (b + s) : ℝ), (b ^ (b - s) : ℝ)
    have hx_pos2 : (b ^ (b + s) : ℝ) > 0 := by positivity 
    have hy_pos2 : (b ^ (b - s) : ℝ) > 0 := by positivity 
    constructor 
    · -- Show x > 0 
      exact_mod_cast hx_pos2 
    constructor 
    · -- Show y > 0 
      exact_mod_cast hy_pos2 
    constructor 
    · -- Show √(x * y) = b ^ b 
      have h3 : (b ^ (b + s) : ℝ) * (b ^ (b - s) : ℝ) = (b ^ b) ^ 2 := by 
        have h4 : (b ^ (b + s) : ℝ) * (b ^ (b - s) : ℝ) = (b) ^ ((b + s) + (b - s) : ℝ) := by 
          rw [← Real.rpow_add]
          ring_nf 
          all_goals linarith 
        have h5 : ((b + s) + (b - s) : ℝ) = (2 * b : ℝ) := by 
          ring_nf 
        rw [h4, h5] 
        have h6 : (b : ℝ) ^ (2 * b : ℝ) = ((b ^ b) ^ 2 : ℝ) := by 
          calc
            (b : ℝ) ^ (2 * b : ℝ) = ((b ^ b : ℝ) ) ^ 2 := by 
              calc 
                (b : ℝ) ^ (2 * b : ℝ) = (b ^ (b : ℝ) ) ^ 2 := by 
                  rw [← Real.rpow_natCast, ← Real.rpow_mul]
                  ring_nf 
                  all_goals linarith 
                _ = ((b ^ b : ℝ) ) ^ 2 := by 
                  norm_num 
            _ = ((b ^ b) ^ 2 : ℝ) := by 
              norm_num 
        linarith [h6]
      have h4 : √((b ^ (b + s) : ℝ) * (b ^ (b - s) : ℝ)) = (b ^ b : ℝ) := by 
        rw [h3] 
        rw [Real.sqrt_sq (by positivity)]
      exact_mod_cast h4 
    · -- Show logb b (x^logb b y) + logb b (y^logb b x) = 4 * b^4
      have h8 : logb b (b ^ (b + s) ) = (b + s) := by
        rw [logb_rpow]
        all_goals 
          try linarith 
          all_goals try
            tauto 
      have h9 : logb b (b ^ (b - s) ) = (b - s) := by
        rw [logb_rpow]
        all_goals 
          try linarith 
          all_goals try
            tauto 
      have h10 : logb b ((b ^ (b + s) ) ^ logb b (b ^ (b - s) )) = logb b (b ^ (b - s) ) * logb b (b ^ (b + s) ) := by 
        rw [logb_rpow_eq_mul_logb_of_pos]
        all_goals positivity 
      have h11 : logb b ((b ^ (b - s) ) ^ logb b (b ^ (b + s) )) = logb b (b ^ (b + s) ) * logb b (b ^ (b - s) ) := by 
        rw [logb_rpow_eq_mul_logb_of_pos]
        all_goals positivity 
      rw [h10, h11, h8, h9]
      nlinarith [h_s_sq]