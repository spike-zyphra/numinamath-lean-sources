import Mathlib

theorem inequalities_325400 (a : ℝ) :
    {x : ℝ | x > 0 ∧ abs (2 * x - 1) - a = 0}.encard = 2 ↔
    a ∈ Set.Ioo 0 1 := by
  constructor
  · -- Assume that the set of positive solutions has cardinality 2, prove $0 < a < 1$
    intro h
    have h1 : a > 0 := by
      by_contra ha
      push_neg at ha
      have ha1 : a ≤ (0 : ℝ) := by linarith
      by_cases ha0 : a < (0 : ℝ)
      · -- Assume a < 0
        have h_eq : {x : ℝ | x > 0 ∧ abs (2 * x - 1) - a = 0} = ∅ := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          intro hx
          rcases hx with ⟨hx1, hx2⟩
          have h_eq1 : abs (2 * x - 1) = a := by linarith
          have h_abs_nonneg : abs (2 * x - 1) ≥ 0 := abs_nonneg (2 * x - 1)
          nlinarith [abs_nonneg (2 * x - 1)]
        rw [h_eq] at h
        simp at h
      · -- Assume a = 0
        have ha00 : a = (0 : ℝ) := by nlinarith
        have h_eq : {x : ℝ | x > 0 ∧ abs (2 * x - 1) - a = 0} = { (1 / 2 : ℝ) } := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
          constructor
          · -- Assume hx
            intro hx
            rcases hx with ⟨hx1, hx2⟩
            have h_eq1 : abs (2 * x - 1) = a := by linarith
            rw [ha00] at h_eq1
            have h_eq3 : abs (2 * x - 1) = (0 : ℝ) := by
              linarith
            have h2 : 2 * x - 1 = (0 : ℝ) := by
              simpa [abs_eq_zero] using h_eq3
            linarith
          · -- Assume x = 1/2
            intro hx
            rw [hx]
            constructor
            · -- Show 1/2 > 0
              norm_num
            · -- Show abs (2 * (1 / 2 : ℝ) - 1) - a = 0
              rw [ha00]
              norm_num [abs]
        rw [h_eq] at h
        simp [Set.encard_singleton] at h
    -- Show $a < 1$
    have h2 : a < (1 : ℝ) := by
      by_contra ha
      push_neg at ha
      have ha1 : a ≥ (1 : ℝ) := by linarith
      have h_eq3 : {x : ℝ | x > 0 ∧ abs (2 * x - 1) - a = 0} = { (a + 1) / 2 } := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · -- Assume hx
          intro hx
          rcases hx with ⟨hx1, hx2⟩
          have h_eq1 : abs (2 * x - 1) = a := by linarith
          by_cases h4 : 2 * x - 1 ≥ 0
          · -- Assume 2 * x - 1 ≥ 0
            have h5 : abs (2 * x - 1) = 2 * x - 1 := abs_of_nonneg h4
            rw [h5] at h_eq1
            have hx5 : x = (a + 1) / 2 := by linarith
            linarith
          · -- Assume 2 * x - 1 < 0
            push_neg at h4
            have h5 : abs (2 * x - 1) = - (2 * x - 1) := abs_of_neg h4
            rw [h5] at h_eq1
            nlinarith
        · -- Assume x = (a + 1) / 2
          intro hx
          rw [hx]
          constructor
          · -- Show x > 0
            nlinarith
          · -- Show abs (2 * ((a + 1) / 2 : ℝ) - 1) - a = 0
            have h3 : 2 * ((a + 1) / 2 : ℝ) - 1 = a := by
              nlinarith
            have h_x_eq : abs (2 * ((a + 1) / 2 : ℝ) - 1) = a := by
              rw [h3]
              rw [abs_of_nonneg (show (a : ℝ) ≥ 0 by linarith)]
            linarith [h_x_eq]
      rw [h_eq3] at h
      simp [Set.encard_singleton] at h
    -- Show $a > 0 \land a < 1$
    exact ⟨h1, h2⟩
  · -- Assume a ∈ (0, 1), show the set of positive solutions has cardinality 2
    rintro ⟨ha1, ha2⟩
    have h_eq : {x : ℝ | x > 0 ∧ abs (2 * x - 1) - a = 0} = { (a + 1) / 2, (1 - a) / 2 } := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · -- Assume hx
        intro hx
        rcases hx with ⟨hx1, hx2⟩
        have h_eq1 : abs (2 * x - 1) = a := by linarith
        by_cases h4 : 2 * x - 1 ≥ 0
        · -- Assume 2 * x - 1 ≥ 0
          have h5 : abs (2 * x - 1) = 2 * x - 1 := abs_of_nonneg h4
          rw [h5] at h_eq1
          left
          linarith
        · -- Assume 2 * x - 1 < 0
          push_neg at h4
          have h5 : abs (2 * x - 1) = - (2 * x - 1) := abs_of_neg h4
          rw [h5] at h_eq1
          right
          linarith
      · -- Case 1: x = (a + 1)/2 or x = (1 - a)/2
        rintro (h | h)
        · -- Case 1: x = (a + 1)/2
          rw [h]
          constructor
          · -- Show x > 0
            nlinarith
          · -- Show abs (2 * ((a + 1) / 2 : ℝ) - 1) - a = 0
            have h3 : 2 * ((a + 1) / 2 : ℝ) - 1 = a := by
              nlinarith
            have h_x_eq : abs (2 * ((a + 1) / 2 : ℝ) - 1) = a := by
              rw [h3]
              rw [abs_of_nonneg (show (a : ℝ) ≥ 0 by linarith)]
            linarith [h_x_eq]
        · -- Case 2: x = (1 - a)/2
          rw [h]
          constructor
          · -- Show x > 0
            nlinarith
          · -- Show abs (2 * ((1 - a) / 2 : ℝ) - 1) - a = 0
            have h3 : 2 * ((1 - a) / 2 : ℝ) - 1 = -a := by
              nlinarith
            have h_x_eq : abs (2 * ((1 - a) / 2 : ℝ) - 1) = a := by
              rw [h3]
              rw [abs_of_nonpos (show (-a : ℝ) ≤ 0 by linarith)]
              all_goals nlinarith
            linarith [h_x_eq]
    rw [h_eq]
    have h3 : ((a + 1 : ℝ) / 2) ≠ ((1 - a : ℝ) / 2) := by
      intro h_eq
      nlinarith
    rw [Set.encard_pair h3]
    all_goals norm_num at h ⊢
    all_goals linarith