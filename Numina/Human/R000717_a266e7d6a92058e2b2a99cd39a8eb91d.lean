import Mathlib

theorem algebra_14251 :
  {b : ℤ | {x : ℤ | x^2 + b * x + 2 ≤ 0}.encard = 3}.encard = 2 := by

  suffices {b : ℤ | {x : ℤ | x^2 + b * x + 2 ≤ 0}.encard = 3} = {-4, 4} by
    rw [this]
    rw [Set.encard_pair]
    simp

  ext b
  simp
  constructor
  . intro hcard
    by_cases hb1 : 4 < b
    . have : {-1, -2, -3, -4} ⊆ {x | x ^ 2 + b * x + 2 ≤ 0} := by
        rintro n (rfl | rfl | rfl | rfl)
        all_goals simp; omega

      apply Set.encard_mono at this
      rw [show ({-1, -2, -3, -4}: Set ℤ).encard = 4 by
        repeat rw [Set.encard_insert_of_not_mem]
        all_goals simp
        norm_num
      ] at this
      rw [hcard] at this
      norm_num at this
    . by_cases hb2 : b < -4
      . have : {1, 2, 3, 4} ⊆ {x | x ^ 2 + b * x + 2 ≤ 0} := by
          rintro n (rfl | rfl | rfl | rfl)
          all_goals simp; omega

        apply Set.encard_mono at this
        rw [show ({1, 2, 3, 4}: Set ℤ).encard = 4 by
          repeat rw [Set.encard_insert_of_not_mem]
          all_goals simp
          norm_num
        ] at this
        rw [hcard] at this
        norm_num at this
      . contrapose hcard
        simp at hb1 hb2 hcard
        have : -3 ≤ b := by omega
        have : b ≤ 3 := by omega
        interval_cases b
        . suffices {x : ℤ | x^2 + -3 * x + 2 ≤ 0} = {1, 2} by
            rw [this, Set.encard_pair]
            . simp
            . norm_num
          ext x
          simp
          constructor
          . intro h
            have : (2*x-3)^2 ≤ 1 := by nlinarith
            have : -1 ≤ 2*x-3 := by nlinarith
            have : 2*x-3 ≤ 1 := by nlinarith
            omega
          . rintro (rfl | rfl)
            all_goals simp

        . suffices {x : ℤ | x^2 + -2 * x + 2 ≤ 0} = ∅ by rw [this]; simp
          ext x
          simp
          nlinarith
        . suffices {x : ℤ | x^2 + -1 * x + 2 ≤ 0} = ∅ by rw [this]; simp
          ext x
          simp
          nlinarith
        . suffices {x : ℤ | x^2 + 0 * x + 2 ≤ 0} = ∅ by rw [this]; simp
          ext x
          simp
          nlinarith
        . suffices {x : ℤ | x^2 + 1 * x + 2 ≤ 0} = ∅ by rw [this]; simp
          ext x
          simp
          nlinarith
        . suffices {x : ℤ | x^2 + 2 * x + 2 ≤ 0} = ∅ by rw [this]; simp
          ext x
          simp
          nlinarith
        . suffices {x : ℤ | x^2 + 3 * x + 2 ≤ 0} = {-1,-2} by
            rw [this, Set.encard_pair]
            . simp
            . norm_num
          ext x
          simp
          constructor
          . intro h
            have : (2*x+3)^2 ≤ 1 := by nlinarith
            have : -1 ≤ 2*x+3 := by nlinarith
            have : 2*x+3 ≤ 1 := by nlinarith
            omega
          . rintro (rfl | rfl)
            all_goals simp


  . rintro (rfl | rfl)
    . suffices {x : ℤ | x^2 + -4 * x + 2 ≤ 0} = {1,2,3} by
        rw [this]
        rw [Set.encard_insert_of_not_mem]
        rw [Set.encard_pair]
        . norm_num
        . simp
        . simp

      ext x
      simp
      constructor
      . intro h
        have : x-2 ≤ 1 := by nlinarith
        have : -1 ≤ x-2 := by nlinarith
        omega

      . rintro (rfl | rfl | rfl)
        all_goals simp

    . suffices {x : ℤ | x^2 + 4 * x + 2 ≤ 0} = {-1,-2,-3} by
        rw [this]
        rw [Set.encard_insert_of_not_mem]
        rw [Set.encard_pair]
        . norm_num
        . simp
        . simp

      ext x
      simp
      constructor
      . intro h
        have : x+2 ≤ 1 := by nlinarith
        have : -1 ≤ x+2 := by nlinarith
        omega

      . rintro (rfl | rfl | rfl)
        all_goals simp
