import Mathlib

theorem algebra_10702 {x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h1 : x ^ y + 1 = y ^ x) (h2 : 2 * x ^ y = y ^ x + 7) :
    (x, y) = (2, 3) := by
  have h3 : x ^ y = 8 := by
    have eq1 : y ^ x = x ^ y + 1 := by
      linarith [h1]
    have eq2 : 2 * x ^ y = y ^ x + 7 := by
      linarith [h2]
    rw [eq1] at eq2
    omega
  have h4 : y ^ x = 9 := by
    have eq1 : y ^ x = x ^ y + 1 := by
      linarith [h1]
    rw [h3] at eq1
    omega
  have h5 : x ≤ 9 := by
    by_contra h
    push_neg at h
    have h6 : x ^ y ≥ 10 ^ y := by
      have h7 : x ≥ 10 := by linarith
      have h8 : x ^ y ≥ 10 ^ y := by
        apply Nat.pow_le_pow_of_le_left
        linarith
      linarith
    have h7 : x ^ y = 8 := h3
    have h8 : 10 ^ y ≥ 10 := by
      have : y ≥ 1 := by
        by_contra h9
        push_neg at h9
        have : y = 0 := by linarith
        omega
      have h10 : 10 ^ y ≥ 10 ^ 1 := by
        apply Nat.pow_le_pow_of_le_right
        norm_num
        omega
      have h9 : 10 ^ 1 = 10 := by norm_num
      linarith [h10, h9]
    nlinarith [h6, h7, h8]
  have h6 : y ≤ 9 := by
    by_contra h
    push_neg at h
    have h7 : y ^ x ≥ 10 ^ x := by
      have h8 : y ≥ 10 := by linarith
      have h9 : y ^ x ≥ 10 ^ x := by
        apply Nat.pow_le_pow_of_le_left
        linarith
      linarith
    have h8 : y ^ x = 9 := h4
    have h9 : 10 ^ x ≥ 10 := by
      have : x ≥ 1 := by
        by_contra h9
        push_neg at h9
        have : x = 0 := by linarith
        omega
      have h10 : 10 ^ x ≥ 10 ^ 1 := by
        apply Nat.pow_le_pow_of_le_right
        norm_num
        omega
      have h9 : 10 ^ 1 = 10 := by norm_num
      linarith [h10, h9]
    nlinarith [h7, h8, h9]
  interval_cases x <;> interval_cases y
    <;> norm_num at h1 h2 h3 h4
    <;> norm_num [Prod.ext_iff]