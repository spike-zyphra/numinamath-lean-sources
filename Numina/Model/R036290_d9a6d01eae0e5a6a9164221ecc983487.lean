import Mathlib

theorem number_theory_134194 (x y : ℕ) (hx : (Nat.digits 10 x).length = 3)
    (hy : (Nat.digits 10 y).length = 3) (hxy : 1000 * x + y = 7 * x * y) :
    x + y = 286 := by
  have h1 : x ≥ 100 := by
    by_contra h
    push_neg at h
    interval_cases x <;> norm_num at hx <;> try { contradiction }
  have h2 : x ≤ 999 := by
    by_contra h
    push_neg at h
    have h3 : (Nat.digits 10 x).length > 3 := by
      have h4 : x ≥ 1000 := by linarith
      have h5 : (Nat.digits 10 x).length = Nat.log 10 x + 1 := by
        rw [Nat.digits_len]
        all_goals omega
      have h6 : Nat.log 10 x ≥ 3 := by
        have h7 : 10 ^ 3 ≤ x := by linarith [h4]
        have h8 : Nat.log 10 x ≥ 3 := by
          apply Nat.le_log_of_pow_le
          all_goals linarith [h7]
        linarith [h8]
      omega
    omega
  have h3 : y ≥ 100 := by
    by_contra h
    push_neg at h
    interval_cases y <;> norm_num at hy <;> try { contradiction }
  have h4 : y ≤ 999 := by
    by_contra h
    push_neg at h
    have h5 : (Nat.digits 10 y).length > 3 := by
      have h6 : y ≥ 1000 := by linarith
      have h7 : (Nat.digits 10 y).length = Nat.log 10 y + 1 := by
        rw [Nat.digits_len]
        all_goals omega
      have h8 : Nat.log 10 y ≥ 3 := by
        have h9 : 10 ^ 3 ≤ y := by linarith [h6]
        have h10 : Nat.log 10 y ≥ 3 := by
          apply Nat.le_log_of_pow_le
          all_goals linarith [h9]
        linarith [h10]
      omega
    omega
  interval_cases x <;> omega