import Mathlib

theorem algebra_278244 (a b p k : ℝ) (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b ∧ b ≠ 1)
    (hp : 0 < p) (hk : 0 < k) :
    Real.logb a p / Real.logb a k = Real.logb b p / Real.logb b k := by

  have h1 : Real.logb a p = Real.log p / Real.log a := by 
    field_simp [Real.logb]

  have h2 : Real.logb a k = Real.log k / Real.log a := by 
    field_simp [Real.logb]

  have h3 : Real.logb b p = Real.log p / Real.log b := by 
    field_simp [Real.logb]

  have h4 : Real.logb b k = Real.log k / Real.log b := by 
    field_simp [Real.logb]

  rw [h1, h2, h3, h4]

  have h5 : Real.log a ≠ 0 := by
    have ha1 : a > 0 := ha.1
    have ha2 : a ≠ 1 := ha.2
    exact Real.log_ne_zero_of_pos_of_ne_one ha1 ha2

  have h6 : Real.log b ≠ 0 := by
    have hb1 : b > 0 := hb.1
    have hb2 : b ≠ 1 := hb.2
    exact Real.log_ne_zero_of_pos_of_ne_one hb1 hb2

  have h7 : (Real.log p / Real.log a) / (Real.log k / Real.log a) = Real.log p / Real.log k := by
    field_simp [show Real.log a ≠ 0 by assumption]

  have h8 : (Real.log p / Real.log b) / (Real.log k / Real.log b) = Real.log p / Real.log k := by
    field_simp [show Real.log b ≠ 0 by assumption]

  rw [h7, h8]
  all_goals linarith [show 0 < p by assumption, show 0 < k by assumption]