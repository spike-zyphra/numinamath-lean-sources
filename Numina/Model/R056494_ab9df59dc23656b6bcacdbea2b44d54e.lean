import Mathlib

theorem inequalities_82212 (a b c d : ℝ) (ha : 0 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a)
    (h : a + d = b + c) (x : ℝ) (hx : 0 < x) :
    x ^ a + x ^ d ≥ x ^ b + x ^ c := by
  have h1 : a - b = c - d := by linarith
  set k := a - b with hk
  have hk_pos : k > 0 := by linarith
  have h2 : c - d = k := by linarith [h1, hk]
  have ha_eq : a = b + k := by linarith
  have hc_eq : c = d + k := by
    nlinarith
  rw [ha_eq, hc_eq]
  have h3 : x ^ (b + k) = x ^ b * x ^ k := by
    rw [Real.rpow_add]
    all_goals linarith
  have h4 : x ^ (d + k) = x ^ d * x ^ k := by
    rw [Real.rpow_add]
    all_goals linarith
  rw [h3, h4]
  have h5 : x ^ b * x ^ k + x ^ d - (x ^ b + x ^ d * x ^ k) = (x ^ b - x ^ d) * (x ^ k - 1) := by
    ring
  have h6 : (x ^ b - x ^ d) * (x ^ k - 1) ≥ 0 := by
    by_cases h7 : x ≥ 1
    · -- Case x ≥ 1
      have hk1 : x ^ k - 1 ≥ 0 := by
        have hk1 : x ^ k ≥ 1 ^ k := by
          apply Real.rpow_le_rpow
          all_goals linarith
        have : (1 : ℝ) ^ k = 1 := by
          simp [Real.one_rpow]
        rw [this] at hk1
        linarith only [hk1]
      have h7 : x ^ b - x ^ d ≥ 0 := by
        have h8 : x ^ b ≥ x ^ d := by
          apply Real.rpow_le_rpow_of_exponent_le
          all_goals linarith
        linarith only [h8]
      nlinarith
    · -- Case 0 < x < 1
      have hk1 : x ^ k - 1 < 0 := by
        have hk1 : x ^ k < 1 ^ k := by
          apply Real.rpow_lt_rpow
          all_goals linarith
        have : (1 : ℝ) ^ k = 1 := by
          simp [Real.one_rpow]
        rw [this] at hk1
        linarith only [hk1]
      have h7 : x ^ b - x ^ d < 0 := by
        have h8 : x ^ b < x ^ d := by
          apply Real.rpow_lt_rpow_of_exponent_gt
          all_goals linarith
        linarith only [h8]
      nlinarith
  linarith [h5, h6]