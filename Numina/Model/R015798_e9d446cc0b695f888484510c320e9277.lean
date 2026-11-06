import Mathlib

theorem inequalities_602949 (a b p q : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hp : 0 < p) (hq : 0 < q) :
    (a ^ (p + q) + b ^ (p + q)) / 2 ≥ ((a ^ p + b ^ p) / 2) * ((a ^ q + b ^ q) / 2) := by

  have h1 : a ^ (p + q) = a ^ p * a ^ q := by
    rw [← Real.rpow_add]
    ring_nf
    all_goals linarith

  have h2 : b ^ (p + q) = b ^ p * b ^ q := by
    rw [← Real.rpow_add]
    ring_nf
    all_goals linarith

  rw [h1, h2]

  have h3 : (a ^ p * a ^ q + b ^ p * b ^ q) / 2 ≥ ((a ^ p + b ^ p) / 2) * ((a ^ q + b ^ q) / 2) := by
    have h4 : (a ^ p * a ^ q + b ^ p * b ^ q) / 2 - ((a ^ p + b ^ p) / 2) * ((a ^ q + b ^ q) / 2) ≥ 0 := by
      have h5 : (a ^ p * a ^ q + b ^ p * b ^ q) / 2 - ((a ^ p + b ^ p) / 2) * ((a ^ q + b ^ q) / 2) = 
        ((a ^ p - b ^ p) * (a ^ q - b ^ q)) / 4 := by
        field_simp
        ring
      rw [h5]
      have h6 : (a ^ p - b ^ p) * (a ^ q - b ^ q) ≥ 0 := by
        by_cases h' : a > b
        · -- If a > b, then a^p > b^p and a^q > b^q
          have h7 : a ^ p > b ^ p := by
            apply Real.rpow_lt_rpow
            all_goals linarith
          have h8 : a ^ q > b ^ q := by
            apply Real.rpow_lt_rpow
            all_goals linarith
          have h9 : (a ^ p - b ^ p) > 0 := by linarith
          have h10 : (a ^ q - b ^ q) > 0 := by linarith
          nlinarith
        by_cases h'' : a = b
        · -- If a = b, then (a^p - b^p) = 0 and (a^q - b^q) = 0
          rw [h'']
          all_goals
            simp
            all_goals linarith
        · -- If a < b
          have h'11 : a < b := by
            by_contra h
            push_neg at h
            have : a = b := by linarith
            tauto
          have h12 : a ^ p < b ^ p := by
            apply Real.rpow_lt_rpow
            all_goals linarith
          have h13 : a ^ q < b ^ q := by
            apply Real.rpow_lt_rpow
            all_goals linarith
          have h14 : (a ^ p - b ^ p) < (0 : ℝ) := by linarith
          have h15 : (a ^ q - b ^ q) < (0 : ℝ) := by linarith
          nlinarith
      positivity
    linarith
    all_goals linarith
  linarith
  all_goals linarith