import Mathlib

theorem algebra_22241 : IsGreatest {x | x < (Real.sqrt 7 + Real.sqrt 5)^6 ∧ ∃ n : ℤ, x = n} 13535 := by
  constructor
  · -- Show 13535 is in the set.
    constructor
    · -- Show 13535 < (Real.sqrt 7 + Real.sqrt 5) ^ 6
      have h1 : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
      have h2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      have h3 : (Real.sqrt 7 + Real.sqrt 5) ^ 2 = 12 + 2 * Real.sqrt 35 := by
        calc
          (Real.sqrt 7 + Real.sqrt 5) ^ 2
            = Real.sqrt 7 ^ 2 + Real.sqrt 5 ^ 2 + 2 * (Real.sqrt 7 * Real.sqrt 5) := by ring
          _ = 7 + 5 + 2 * (Real.sqrt 7 * Real.sqrt 5) := by rw [h1, h2]
          _ = 12 + 2 * (Real.sqrt 7 * Real.sqrt 5) := by norm_num
          _ = 12 + 2 * Real.sqrt 35 := by
            have h4 : Real.sqrt 7 * Real.sqrt 5 = Real.sqrt 35 := by
              rw [← Real.sqrt_mul (by norm_num)]
              all_goals norm_num
            rw [h4]
      have h4 : (Real.sqrt 7 + Real.sqrt 5) ^ 6 = ( (Real.sqrt 7 + Real.sqrt 5) ^ 2 ) ^ 3 := by ring
      rw [h4, h3]
      nlinarith [show 0 < (Real.sqrt 35 : ℝ) by positivity, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (35 : ℝ) by norm_num)
        ]
    · -- Show that there exists an integer n such that 13535 = n
      use 13535
      all_goals norm_num
  · -- Show that for any x in the set, x ≤ 13535
    intro x hx
    rcases hx with ⟨hx1, ⟨n, h1⟩⟩
    have h2 : (Real.sqrt 7 + Real.sqrt 5) ^ 6 < (13536 : ℝ) := by
      have h1' : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
      have h2' : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      have h3 : (Real.sqrt 7 + Real.sqrt 5) ^ 2 = 12 + 2 * Real.sqrt 35 := by
        calc
          (Real.sqrt 7 + Real.sqrt 5) ^ 2
            = Real.sqrt 7 ^ 2 + Real.sqrt 5 ^ 2 + 2 * (Real.sqrt 7 * Real.sqrt 5) := by ring
          _ = 7 + 5 + 2 * (Real.sqrt 7 * Real.sqrt 5) := by rw [h1', h2']
          _ = 12 + 2 * (Real.sqrt 7 * Real.sqrt 5) := by norm_num
          _ = 12 + 2 * Real.sqrt 35 := by
            have h4 : Real.sqrt 7 * Real.sqrt 5 = Real.sqrt 35 := by
              rw [← Real.sqrt_mul (by norm_num)]
              all_goals norm_num
            rw [h4]
      have h4 : (Real.sqrt 7 + Real.sqrt 5) ^ 6 = ( (Real.sqrt 7 + Real.sqrt 5) ^ 2 ) ^ 3 := by ring
      rw [h4, h3]
      nlinarith [show 0 < (Real.sqrt 35 : ℝ) by positivity, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (35 : ℝ) by norm_num)
        ]
    have h2' : (n : ℝ) < (13536 : ℝ) := by
      nlinarith
    have h3 : n < 13536 := by
      exact_mod_cast h2'
    have h4 : n ≤ 13535 := by 
      omega
    have h5 : (n : ℝ) ≤ (13535 : ℝ) := by 
      exact_mod_cast h4
    linarith [h1, h5]