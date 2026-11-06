import Mathlib

theorem number_theory_59646 (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : x ^ 4 + y ^ 4 = 4721) :
    x + y = 13 := by
  have h1 : x ≤ 8 := by
    by_contra h2
    push_neg at h2
    have h3 : x ≥ 9 := by linarith
    have h4 : x ^ 4 ≥ 6561 := by
      have h5 : x ^ 4 ≥ 9 ^ 4 := by
        apply Nat.pow_le_pow_of_le_left
        linarith  -- To get $x \geq 9$ from h3
        all_goals linarith
      have h6 : 9 ^ 4 = 6561 := by norm_num
      linarith
    have h7 : y ^ 4 ≥ 0 := by positivity
    have h8 : x ^ 4 + y ^ 4 ≥ 6561 := by linarith [h4, h7]
    linarith
  have h2 : y ≤ 8 := by
    by_contra h3
    push_neg at h3
    have h4 : y ≥ 9 := by linarith
    have h5 : y ^ 4 ≥ 6561 := by
      have h6 : y ^ 4 ≥ 9 ^ 4 := by
        apply Nat.pow_le_pow_of_le_left
        linarith  -- To get $y \geq 9$ from h4
        all_goals linarith
      have h7 : 9 ^ 4 = 6561 := by norm_num
      linarith
    have h6 : x ^ 4 ≥ 0 := by positivity
    have h7 : x ^ 4 + y ^ 4 ≥ 6561 := by linarith [h6, h5]
    linarith
  -- Now manually check all possible values
  interval_cases x <;> interval_cases y
  <;> omega