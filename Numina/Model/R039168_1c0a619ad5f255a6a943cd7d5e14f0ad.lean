import Mathlib

theorem algebra_190503 (x y : ℕ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : 72 / x = 72 / y + 1 * 60 + 48) (h2 : 36 / x = 36 / y + 1 * 60 + 48 - 6 * 60) :
    x = 4 ∧ y = 4 := by
  norm_num at h1 h2
  have h3 : x ≤ 72 := by
    by_contra h
    push_neg at h
    have h3 : 72 / x = 0 := by
      rw [Nat.div_eq_zero_iff]
      omega
    rw [h3] at h1
    have h4 : 72 / y ≤ 108 := by
      omega
    have h4 : y ≤ 72 := by
      by_contra h
      push_neg at h
      have h5 : 72 / y = 0 := by
        rw [Nat.div_eq_zero_iff]
        omega
      omega
    interval_cases y <;> omega
  have h4 : y ≤ 72 := by
    by_contra h
    push_neg at h
    have h5 : 72 / y = 0 := by
      rw [Nat.div_eq_zero_iff]
      omega
    rw [h5] at h1
    have h3 : 72 / x ≤ 108 := by
      omega
    have h3 : x ≤ 72 := by
      by_contra h
      push_neg at h
      have h3 : 72 / x = 0 := by
        rw [Nat.div_eq_zero_iff]
        omega
      omega
    interval_cases x <;> omega
  interval_cases x <;> try { 
    omega 
  } <;> try { 
    interval_cases y 
    all_goals 
      omega 
  }