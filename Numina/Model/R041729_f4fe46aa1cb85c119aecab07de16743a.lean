import Mathlib



theorem algebra_240748 : {x : ℤ | (2:ℝ) ^ x * (4 - x) = 2 * x + 4} = {0, 1, 2} := by
  ext x
  simp
  constructor
  .
    intro h
    have x_ne_4: x ≠ 4 := by
      by_contra x_eq_4
      rw [x_eq_4] at h
      norm_num at h
    -- $x \in \{-2, -1, 0, 1, 2, 3, 4\}$.
    have h6 : x ≤ 4 := by
      by_contra h6
      push_neg at h6
      have h6' : x ≥ 5 := by omega
      have h6'' : x ≥ 5 := by omega
      have h7 : (4 - (x : ℝ)) < 0 := by
        have h7' : (x : ℝ) ≥ (5 : ℝ) := by
          exact_mod_cast h6''
        linarith
      have h8 : (2 : ℝ) ^ x * (4 - ↑x) < 0 := by
        have h9 : (2 : ℝ) ^ x > 0 := by positivity
        nlinarith
      have h9 : (2 * ↑x + 4) ≥ 14 := by
        have h9' : (x : ℝ) ≥ (5 : ℝ) := by
          exact_mod_cast h6''
        linarith
      nlinarith [h, h9]
    have h7 : x ≥ -2 := by
      by_contra h7
      push_neg at h7
      have h7' : x ≤ -3 := by omega
      have h7'' : x ≤ -3 := by omega
      have h8 : (4 - (x : ℝ)) > 0 := by
        have h8' : (x : ℝ) ≤ (-3 : ℝ) := by
          exact_mod_cast h7''
        linarith
      have h6 : (2 * ↑x + 4 : ℝ) ≤ -2 := by
        have h6' : (x : ℝ) ≤ (-3 : ℝ) := by
          exact_mod_cast h7''
        linarith
      have h5 : (2 : ℝ) ^ x > 0 := by positivity
      have h4 : (2 : ℝ) ^ x * (4 - ↑x) > 0 := by
        apply mul_pos
        linarith
        linarith
      nlinarith [h, h4, h6]
    have h5 : x ≥ -2 := by omega
    have h6 : x ≤ 4 := by omega
    interval_cases x <;> norm_num at h ⊢
  .
    rintro (rfl | rfl | rfl)
    norm_num
    norm_num
    norm_num