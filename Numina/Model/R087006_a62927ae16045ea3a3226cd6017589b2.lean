import Mathlib

theorem algebra_228779 (a b x : ℝ) (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b ∧ b ≠ 1)
    (hx : 0 < x) :
    Real.logb a x = Real.logb b x / Real.logb b a ∧
    Real.logb a b = 1 / Real.logb b a := by

  constructor

  · -- Proof that $\log_a x = \frac{\log_b x}{\log_b a}$

    have h1 : Real.logb a x = Real.log x / Real.log a := by
      field_simp [Real.logb]

    have h2 : Real.logb b x = Real.log x / Real.log b := by
      field_simp [Real.logb]

    have h3 : Real.logb b a = Real.log a / Real.log b := by
      field_simp [Real.logb]

    rw [h1, h2, h3]

    field_simp [(show Real.log b ≠ 0 by
        apply Real.log_ne_zero_of_pos_of_ne_one hb.1 hb.2),
        (show Real.log a ≠ 0 by
          apply Real.log_ne_zero_of_pos_of_ne_one ha.1 ha.2)]

    all_goals linarith

  · -- Proof that $\log_a b = \frac{1}{\log_b a}$

    have h1 : Real.logb a b = Real.log b / Real.log a := by
      field_simp [Real.logb]

    have h2 : Real.logb b a = Real.log a / Real.log b := by
      field_simp [Real.logb]

    rw [h1, h2]

    field_simp [(show Real.log b ≠ 0 by
        apply Real.log_ne_zero_of_pos_of_ne_one hb.1 hb.2),
        (show Real.log a ≠ 0 by
          apply Real.log_ne_zero_of_pos_of_ne_one ha.1 ha.2)]

    all_goals linarith