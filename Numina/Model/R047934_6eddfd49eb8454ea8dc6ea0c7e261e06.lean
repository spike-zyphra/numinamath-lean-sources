import Mathlib

theorem algebra_10928 : IsLeast { abs (a - b) | (a : ℤ) (b : ℤ) (h : a * b - 3 * a + 4 * b = 137) } 13 := by
  constructor
  · -- Show 13 is in the set.
    use 21, 8
    norm_num
  · -- Show 13 is minimal.
    intro k hk
    rcases hk with ⟨a, b, h, hk⟩
    by_contra h1
    push_neg at h1
    -- Assume |a - b| < 13, derive a contradiction
    have h2 : a * b - 3 * a + 4 * b = 137 := h
    have eq1 : (a + 4) * (b - 3) = 125 := by 
      linarith
    have h3 : a + 4 ∣ 125 := by
      use b - 3 
      all_goals linarith
    have h4 : (a + 4) = 1 ∨ (a + 4) = 5 ∨ (a + 4) = 25 ∨ (a + 4) = 125 ∨ (a + 4) = -1 ∨ (a + 4) = -5 ∨ (a + 4) = -25 ∨ (a + 4) = -125 := by
      have h5 : (a + 4) ∣ 125 := h3 
      have h6 : (a + 4) ∣ 125 := h5 
      have : (a + 4) ≤ 125 := by 
        apply Int.le_of_dvd (by norm_num) h6 
      have : (a + 4) ≥ -125 := by 
        have h7 : (- (a + 4)) ∣ 125 := by 
          exact Int.neg_dvd.2 h6 
        have h8 : (- (a + 4)) ≤ 125 := by 
          apply Int.le_of_dvd (by norm_num) h7 
        linarith 
      interval_cases (a + 4) <;> tauto 
    rcases h4 with (h| h| h| h| h| h| h| h)
    · -- Case (a + 4) = 1, so b - 3 = 125.
      have hx1 : b - 3 = 125 := by 
        rw [h] at eq1 
        nlinarith 
      have ha1 : a = -3 := by 
        omega 
      have hb1 : b = 128 := by 
        omega 
      have h7 : abs (a - b) = 131 := by
        rw [ha1, hb1]
        norm_num 
      omega
    · -- Case (a + 4) = 5, so b - 3 = 25.
      have hx2 : b - 3 = 25 := by 
        rw [h] at eq1 
        nlinarith 
      have ha2 : a = 1 := by 
        omega 
      have hb2 : b = 28 := by 
        omega 
      have h7 : abs (a - b) = 27 := by
        rw [ha2, hb2]
        norm_num 
      omega 
    · -- Case (a + 4) = 25, so b - 3 = 5.
      have hx3 : b - 3 = 5 := by 
        rw [h] at eq1 
        nlinarith 
      have ha3 : a = 21 := by 
        omega 
      have hb3 : b = 8 := by 
        omega 
      have h7 : abs (a - b) = 13 := by
        rw [ha3, hb3]
        norm_num 
      omega 
    · -- Case (a + 4) = 125, so b - 3 = 1.
      have hx4 : b - 3 = 1 := by 
        rw [h] at eq1 
        nlinarith 
      have ha4 : a = 121 := by 
        omega 
      have hb4 : b = 4 := by 
        omega 
      have h7 : abs (a - b) = 117 := by
        rw [ha4, hb4]
        norm_num 
      omega 
    · -- Case (a + 4) = -1, so b - 3 = -125.
      have hx5 : b - 3 = -125 := by 
        rw [h] at eq1 
        nlinarith 
      have ha5 : a = -5 := by 
        omega 
      have hb5 : b = -122 := by 
        omega 
      have h7 : abs (a - b) = 117 := by
        rw [ha5, hb5]
        norm_num 
      omega 
    · -- Case (a + 4) = -5, so b - 3 = -25.
      have hx6 : b - 3 = -25 := by 
        rw [h] at eq1 
        nlinarith 
      have ha6 : a = -9 := by 
        omega 
      have hb6 : b = -22 := by 
        omega 
      have h7 : abs (a - b) = 13 := by
        rw [ha6, hb6]
        norm_num 
      omega
    · -- Case (a + 4) = -25, so b - 3 = -5.
      have hx7 : b - 3 = -5 := by 
        rw [h] at eq1 
        nlinarith 
      have ha7 : a = -29 := by 
        omega 
      have hb7 : b = -2 := by 
        omega 
      have h7 : abs (a - b) = 27 := by
        rw [ha7, hb7]
        norm_num 
      omega 
    · -- Case (a + 4) = -125, so b - 3 = -1.
      have hx8 : b - 3 = -1 := by 
        rw [h] at eq1 
        nlinarith 
      have ha8 : a = -129 := by 
        omega 
      have hb8 : b = 2 := by 
        omega 
      have h7 : abs (a - b) = 131 := by 
        rw [ha8, hb8]
        norm_num 
      omega