import Mathlib

theorem algebra_143066 {a b c : ℝ} (habc : a * b * c > 0) :
    (|a| / a + |b| / b + |c| / c - a * b * c / |a * b * c|) = 2 ∨
    (|a| / a + |b| / b + |c| / c - a * b * c / |a * b * c|) = -2 := by
  have ha : a ≠ 0 := by
    by_contra h
    have h1 : a * b * c = 0 := by 
      rw [h]
      norm_num
    linarith
  have hb : b ≠ 0 := by
    by_contra h
    have h1 : a * b * c = 0 := by
      rw [h]
      norm_num
    linarith
  have hc : c ≠ 0 := by
    by_contra h
    have h1 : a * b * c = 0 := by 
      rw [h]
      norm_num
    linarith
  have h4 : a * b * c / |a * b * c| = 1 := by
    have h5 : |a * b * c| = a * b * c := by
      rw [abs_of_pos habc]
    have h6 : a * b * c / |a * b * c| = 1 := by
      rw [h5]
      field_simp [show a * b * c ≠ 0 by positivity]
    exact h6
  have h5 : (|a| / a + |b| / b + |c| / c) = 3 ∨ (|a| / a + |b| / b + |c| / c) = -1 := by
    by_cases ha1 : a > 0
    · -- If a > 0, determine signs of b and c based on product
      by_cases hb1 : b > 0
      · -- If a > 0, b > 0, then c > 0 (from abc > 0)
        have hc1 : c > 0 := by
          have h_pos : a * b * c > 0 := habc
          have pos1 : a * b > 0 := by positivity
          nlinarith
        have h6 : |a| / a = 1 := by
          rw [abs_of_pos ha1]
          field_simp [ha]
        have h7 : |b| / b = 1 := by
          rw [abs_of_pos hb1]
          field_simp [hb]
        have h8 : |c| / c = 1 := by
          rw [abs_of_pos hc1]
          field_simp [hc]
        left
        linarith
      · -- If a > 0, b ≤ 0, then b < 0
        have hb2 : b < 0 := by
          by_contra h
          push_neg at h
          have : b = 0 := by linarith
          contradiction
        have hc2 : c < 0 := by
          have h_pos : a * b * c > 0 := habc
          have neg1 : b < 0 := hb2
          have pos1 : a * b < 0 := by nlinarith
          nlinarith
        have h6 : |a| / a = 1 := by
          rw [abs_of_pos ha1]
          field_simp [ha]
        have h7 : |b| / b = -1 := by
          rw [abs_of_neg hb2]
          field_simp [hb]
        have h8 : |c| / c = -1 := by
          rw [abs_of_neg hc2]
          field_simp [hc]
        right
        linarith
    · -- If a ≤ 0, then a < 0
      have ha2 : a < 0 := by
        by_contra h
        push_neg at h
        have : a = 0 := by linarith
        contradiction
      by_cases hb1 : b > 0
      · -- If a < 0, b > 0
        have hc2 : c < 0 := by
          have h_pos : a * b * c > 0 := habc
          have neg1 : a < 0 := ha2
          have pos1 : b > 0 := hb1
          have pos2 : a * b < 0 := by nlinarith
          nlinarith
        have h6 : |a| / a = -1 := by
          rw [abs_of_neg ha2]
          field_simp [ha]
        have h7 : |b| / b = 1 := by
          rw [abs_of_pos hb1]
          field_simp [hb]
        have h8 : |c| / c = -1 := by
          rw [abs_of_neg hc2]
          field_simp [hc]
        right
        linarith
      · -- If a < 0, b ≤ 0, hence b < 0
        have hb2 : b < 0 := by
          by_contra h
          push_neg at h
          have : b = 0 := by linarith
          contradiction
        have hc1 : c > 0 := by
          have h_pos : a * b * c > 0 := habc
          have neg1 : a < 0 := ha2
          have neg2 : b < 0 := hb2
          have pos2 : a * b > 0 := by nlinarith
          nlinarith
        have h6 : |a| / a = -1 := by
          rw [abs_of_neg ha2]
          field_simp [ha]
        have h7 : |b| / b = -1 := by
          rw [abs_of_neg hb2]
          field_simp [hb]
        have h8 : |c| / c = 1 := by
          rw [abs_of_pos hc1]
          field_simp [hc]
        right
        linarith
  rcases h5 with h5 | h5
  · -- Case 1: sum = 3
    left
    linarith [h5, h4]
  · -- Case 2: sum = -1
    right
    linarith [h5, h4]