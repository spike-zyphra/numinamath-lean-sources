import Mathlib

theorem algebra_297647 (x y z : ℤ) :
    x + y + z = 0 ∧ x^3 + y^3 + z^3 = -18 ↔
    (x = 1 ∧ y = 2 ∧ z = -3) ∨ (x = 2 ∧ y = 1 ∧ z = -3) ∨
    (x = 1 ∧ y = -3 ∧ z = 2) ∨ (x = 2 ∧ y = -3 ∧ z = 1) ∨
    (x = -3 ∧ y = 1 ∧ z = 2) ∨ (x = -3 ∧ y = 2 ∧ z = 1) := by
  constructor
  · -- Assume the equations hold, prove the disjunction of the solutions
    rintro ⟨h1, h2⟩
    have h3 : x * y * z = -6 := by
      have h4 : x^3 + y^3 + z^3 = 3 * (x * y * z) := by
        have h5 : x + y + z = 0 := h1
        have h6 : x^3 + y^3 + z^3 - 3 * (x * y * z) = (x + y + z) * (x^2 + y^2 + z^2 - (x * y + y * z + z * x)) := by
          ring
        rw [h5] at h6
        linarith
      linarith [h4, h2]
    have h4 : x ≤ 6 := by
      have h5 : x ∣ -6 := by
        use y * z
        nlinarith [h3]
      have h6 : x ∣ 6 := by
        exact Int.dvd_neg.mp h5
      have h7 : x ≤ 6 := by
        apply Int.le_of_dvd (show (0 : ℤ) < 6 by norm_num) h6
      linarith
    have h5 : y ≤ 6 := by
      have h6 : y ∣ -6 := by
        use x * z
        nlinarith [h3]
      have h7 : y ∣ 6 := by
        exact Int.dvd_neg.mp h6
      have h8 : y ≤ 6 := by
        apply Int.le_of_dvd (show (0 : ℤ) < 6 by norm_num) h7
      linarith
    have h7 : z ≤ 6 := by
      have h8 : z ∣ -6 := by
        use x * y
        nlinarith [h3]
      have h9 : z ∣ 6 := by
        exact Int.dvd_neg.mp h8
      have h10 : z ≤ 6 := by
        apply Int.le_of_dvd (show (0 : ℤ) < 6 by norm_num) h9
      linarith
    have h6 : x ≥ -6 := by
      have h5 : x ∣ -6 := by
        use y * z
        nlinarith [h3]
      have h6 : x ∣ 6 := by
        exact Int.dvd_neg.mp h5
      have h8 : x ≥ -6 := by
        have h9 : -x ∣ 6 := by 
          exact Int.neg_dvd.2 h6
        have h10 : -x ≤ 6 := by
          apply Int.le_of_dvd (show (0 : ℤ) < 6 by norm_num) h9
        omega
      linarith
    have h8 : y ≥ -6 := by
      have h7 : y ∣ -6 := by
        use x * z
        nlinarith [h3]
      have h8 : y ∣ 6 := by
        exact Int.dvd_neg.mp h7
      have h10 : y ≥ -6 := by
        have h11 : -y ∣ 6 := by 
          exact Int.neg_dvd.2 h8
        have h12 : -y ≤ 6 := by
          apply Int.le_of_dvd (show (0 : ℤ) < 6 by norm_num) h11
        omega
      linarith
    have h9 : z ≥ -6 := by
      have h8 : z ∣ -6 := by
        use x * y
        nlinarith [h3]
      have h9 : z ∣ 6 := by
        exact Int.dvd_neg.mp h8
      have h12 : z ≥ -6 := by
        have h13 : -z ∣ 6 := by 
          exact Int.neg_dvd.2 h9
        have h14 : -z ≤ 6 := by
          apply Int.le_of_dvd (show (0 : ℤ) < 6 by norm_num) h13
        omega
      linarith
    interval_cases x <;> interval_cases y <;> omega
  · -- Assume one of the solutions holds, prove the equations
    rintro (h | h | h | h | h | h)
    · -- Check the first solution
      rcases h with ⟨hx, hy, hz⟩
      constructor
      · -- Check x + y + z = 0
        linarith
      · -- Check x^3 + y^3 + z^3 = -18
        rw [hx, hy, hz]
        norm_num
    · -- Check the second solution
      rcases h with ⟨hx, hy, hz⟩
      constructor
      · -- Check x + y + z = 0
        linarith
      · -- Check x^3 + y^3 + z^3 = -18
        rw [hx, hy, hz]
        norm_num
    · -- Check the third solution
      rcases h with ⟨hx, hy, hz⟩
      constructor
      · -- Check x + y + z = 0
        linarith
      · -- Check x^3 + y^3 + z^3 = -18
        rw [hx, hy, hz]
        norm_num
    · -- Check the fourth solution
      rcases h with ⟨hx, hy, hz⟩
      constructor
      · -- Check x + y + z = 0
        linarith
      · -- Check x^3 + y^3 + z^3 = -18
        rw [hx, hy, hz]
        norm_num
    · -- Check the fifth solution
      rcases h with ⟨hx, hy, hz⟩
      constructor
      · -- Check x + y + z = 0
        linarith
      · -- Check x^3 + y^3 + z^3 = -18
        rw [hx, hy, hz]
        norm_num
    · -- Check the sixth solution
      rcases h with ⟨hx, hy, hz⟩
      constructor
      · -- Check x + y + z = 0
        linarith
      · -- Check x^3 + y^3 + z^3 = -18
        rw [hx, hy, hz]
        norm_num