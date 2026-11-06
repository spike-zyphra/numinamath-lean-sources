import Mathlib

theorem algebra_1408 {x y z : ℤ} (h₀ : x ≤ y) (h₁ : y ≤ z) (h₂ : abs (x + y) + abs (y + z) + abs (z + x) = 4) (h₃ : abs (x - y) + abs (y - z) + abs (z - x) = 2) :
    x^2 + y^2 + z^2 = 2 := by

  have h4 : abs (x - y) = y - x := by 
    rw [abs_of_nonpos (by linarith)]
    all_goals omega

  have h5 : abs (y - z) = z - y := by 
    rw [abs_of_nonpos (by linarith)]
    all_goals omega

  have h6 : abs (z - x) = z - x := by 
    rw [abs_of_nonneg (by linarith)]
    all_goals omega

  have h7 : z = x + 1 := by 
    rw [h4, h5, h6] at h₃ 
    linarith

  have h8 : abs (x + y) + abs (y + z) + abs (z + x) = 4 := h₂

  rw [show z = x + 1 by linarith [h7] ] at h8

  have h9 : abs (x + y) + abs (y + x + 1) + abs (2 * x + 1) = 4 := by 
    ring_nf at h8 ⊢ 
    all_goals omega

  by_cases h10 : x + y ≥ 0 
  · -- Case 1: x + y ≥ 0 
    have h11 : abs (x + y) = x + y := by 
      rw [abs_of_nonneg h10]

    have h12 : abs (y + x + 1) = y + x + 1 := by 
      have h13 : y + x + 1 ≥ 0 := by 
        nlinarith 
      rw [abs_of_nonneg h13]

    rw [h11, h12] at h9

    by_cases h14 : 2 * x + 1 ≥ 0 
    · -- Case 1a: 2x + 1 ≥ 0 
      have h15 : abs (2 * x + 1) = 2 * x + 1 := by 
        rw [abs_of_nonneg h14]
      rw [h15] at h9 
      have h17 : 2 * x + y = 1 := by 
        nlinarith
      have h19 : x = 0 := by 
        nlinarith [show y ≤ z by linarith, show z = x + 1 by linarith [h7], h17]
      have h20 : y = 1 := by 
        linarith [h17, h19]
      have h21 : z = 1 := by 
        linarith [h7, h19]
      rw [h19, h20, h21]
      all_goals norm_num

    · -- Case 1b: 2x + 1 < 0 
      have h15 : abs (2 * x + 1) = - (2 * x + 1) := by 
        rw [abs_of_neg (by linarith)]
      rw [h15] at h9 
      nlinarith [show y ≤ z by linarith, show z = x + 1 by linarith [h7]]

  · -- Case 2: x + y < 0 
    push_neg at h10 
    have h11 : abs (x + y) = - (x + y) := by 
      rw [abs_of_neg h10]

    rw [h11] at h9 

    by_cases h14 : x + y + 1 ≥ 0 
    · -- Case 2a: x + y + 1 ≥ 0 
      have h12 : abs (y + x + 1) = y + x + 1 := by 
        have h14' : y + x + 1 ≥ 0 := by 
          omega 
        have h16' : abs (y + x + 1) = y + x + 1 := by 
          rw [abs_of_nonneg h14']
          <;> try { ring }
        exact h16'

      rw [h12] at h9 
      have h17 : abs (2 * x + 1) = 3 := by 
        omega 
      cases' eq_or_eq_neg_of_abs_eq h17 with h18 h19 
      · -- Case 2a1: 2x + 1 = 3 
        have h20 : x = 1 := by 
          linarith 
        nlinarith [show x + y < 0 by linarith, show y ≥ x by linarith, show y ≤ z by linarith, show z = x + 1 by linarith [h7], h20]

      · -- Case 2a2: 2x + 1 = -3 
        have h20 : x = -2 := by 
          linarith 
        nlinarith [show x + y < 0 by linarith, show y ≥ x by linarith, show y ≤ z by linarith, show z = x + 1 by linarith [h7], h20]

    · -- Case 2b: x + y + 1 < 0 
      push_neg at h14 
      have h12 : abs (y + x + 1) = - (y + x + 1) := by 
        have h13 : y + x + 1 < 0 := by 
          omega 
        rw [abs_of_neg h13]
      rw [h12] at h9 
      by_cases h15 : 2 * x + 1 ≥ 0 
      · -- Case 2b1: 2x + 1 ≥ 0 
        have h16 : abs (2 * x + 1) = 2 * x + 1 := by 
          rw [abs_of_nonneg h15]
        rw [h16] at h9 
        nlinarith [show x + y < 0 by linarith, show y ≥ x by linarith, show y ≤ z by linarith, show z = x + 1 by linarith [h7]]

      · -- Case 2b2: 2x + 1 < 0 
        have h16 : abs (2 * x + 1) = - (2 * x + 1) := by 
          rw [abs_of_neg (by linarith)]
        rw [h16] at h9 
        have h19 : x = -1 := by 
          nlinarith 
        have h20 : y = -1 := by 
          nlinarith [h19, show x + y < 0 by linarith]
        have h21 : z = 0 := by 
          linarith [h7, h19]
        rw [h19, h20, h21]
        all_goals norm_num