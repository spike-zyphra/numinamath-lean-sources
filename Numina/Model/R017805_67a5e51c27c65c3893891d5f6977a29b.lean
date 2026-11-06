import Mathlib

theorem algebra_301053 : (Nat.floor ((Real.sqrt 6 + Real.sqrt 5)^6)) = 10581 := by
  have h1 : Nat.floor ((Real.sqrt 6 + Real.sqrt 5) ^ 6) = 10581 := by
    have h2 : Real.sqrt 6 + Real.sqrt 5 > 0 := by positivity
    have h3 : (Real.sqrt 6 + Real.sqrt 5) ^ 2 = 11 + 2 * Real.sqrt 30 := by
      calc
        (Real.sqrt 6 + Real.sqrt 5) ^ 2 = (Real.sqrt 6) ^ 2 + (Real.sqrt 5) ^ 2 + 2 * (Real.sqrt 6 * Real.sqrt 5) := by ring
        _ = 6 + 5 + 2 * (Real.sqrt 6 * Real.sqrt 5) := by
          have h6 : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)
          have h5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)
          rw [h6, h5]
          all_goals nlinarith
          all_goals nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 5]
        _ = 11 + 2 * (Real.sqrt 6 * Real.sqrt 5) := by ring
        _ = 11 + 2 * Real.sqrt 30 := by
          have h8 : Real.sqrt 6 * Real.sqrt 5 = Real.sqrt 30 := by
            have h9 : Real.sqrt 6 * Real.sqrt 5 = Real.sqrt (6 * 5 : ℝ) := by 
              rw [← Real.sqrt_mul (by norm_num)]
            rw [h9]
            all_goals norm_num
          rw [h8]
    -- Calculate h5 as (√6 + √5)^6
    -- basically we need to calculate { (√6+√5)^2 = 11 + 2√30, (√6 + √5)^4 = (11 + 2√30)^2, and (√6 + √5)^6 = (√6+√5)^2 * (√6+√5)^4 
    have h4 : (Real.sqrt 6 + Real.sqrt 5) ^ 4 = (11 + 2 * Real.sqrt 30) ^ 2 := by
      calc
        (Real.sqrt 6 + Real.sqrt 5) ^ 4 = ((Real.sqrt 6 + Real.sqrt 5) ^ 2) ^ 2 := by ring
        _ = (11 + 2 * Real.sqrt 30) ^ 2 := by rw [h3]
    -- Calculate h5 as (√6 + √5)^6
    have h5 : (Real.sqrt 6 + Real.sqrt 5) ^ 6 = (Real.sqrt 6 + Real.sqrt 5) ^ 2 * (Real.sqrt 6 + Real.sqrt 5) ^ 4 := by ring
    rw [h5]
    rw [h3, h4]
    -- Now we need to simplify ((11 + 2 * √30)^2)
    -- which will give us something like 10581.875 which floor is 10581
    -- in the concrete computationally half-closed interval form
    have h6 : (11 + 2 * Real.sqrt 30 : ℝ) ^ 2 = 121 + 44 * Real.sqrt 30 + 4 * (Real.sqrt 30) ^ 2 := by ring
    have h7 : (Real.sqrt 30 : ℝ) ^ 2 = 30 := Real.sq_sqrt (show (0 : ℝ) ≤ (30 : ℝ) by norm_num)
    have h10 : (11 + 2 * Real.sqrt 30 : ℝ) ^ 2 = 121 + 44 * Real.sqrt 30 + 120 := by
      rw [h6]
      rw [h7]
      all_goals nlinarith [h7, h6, Real.sqrt_nonneg 30]
    -- The intermediate value of (√5+√6)^6 is (11 + 2√30)^2, which is calculated step-by-step here
    -- Finally the full value is computed directly for native_decide
    have h8 : (Real.sqrt 6 + Real.sqrt 5) ^ 6 > (10581 : ℝ) := by
      nlinarith [h5, h3, h4, h6, h7, h10, Real.sqrt_nonneg 30, Real.sqrt_nonneg 5, Real.sqrt_nonneg 6, 
        Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), 
        sq_nonneg (Real.sqrt 5 - Real.sqrt 6), 
        mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 6), 
        mul_pos (show Real.sqrt 5 > 0 by positivity) (show Real.sqrt 6 > 0 by positivity), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (30 : ℝ) by norm_num)
      ]
    have h9 : (Real.sqrt 6 + Real.sqrt 5) ^ 6 < (10582 : ℝ) := by
      nlinarith [h5, h3, h4, h6, h7, h10, Real.sqrt_nonneg 30, Real.sqrt_nonneg 5, Real.sqrt_nonneg 6, 
        Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), 
        sq_nonneg (Real.sqrt 5 - Real.sqrt 6), 
        mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 6), 
        mul_pos (show Real.sqrt 5 > 0 by positivity) (show Real.sqrt 6 > 0 by positivity), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (30 : ℝ) by norm_num)
      ]
    -- Now proving Nat.floor ((√5 + √6) ^ 6) = 10581
    rw [Nat.floor_eq_iff]
    constructor <;> (try norm_num) <;> try linarith [h8, h9]
    all_goals nlinarith [h8, h9, Real.sqrt_nonneg 5, Real.sqrt_nonneg 6, 
      Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)
    ]
  exact h1
  all_goals try { tauto } <;> try { linarith } <;> try { nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)] } <;> try { norm_num }
  <;> try { ring_nf } <;> try { norm_num [Real.sqrt_nonneg, mul_self_eq_sq] } <;> try { nlinarith }
  <;> try { try { tauto } } <;> try { try { tauto } }
  <;> try { tauto } <;> try { linarith }
  <;> try { tauto } <;> try { linarith }
  <;> try { tauto } <;> try { nlinarith }
  <;> try { tauto } <;> try { linarith }
  <;> try { tauto }