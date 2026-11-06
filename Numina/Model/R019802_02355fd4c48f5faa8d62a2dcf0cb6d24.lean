import Mathlib

theorem algebra_259631 {x : ℕ} (hx : x ≠ 0) (h : 97 + x * (19 + 91 / x) = 321) :
    x = 7 := by
  have h1 : x ≤ 91 := by
    by_contra h2
    push_neg at h2
    have h2' : 91 / x = 0 := by
      rw [Nat.div_eq_zero_iff]
      omega
    simp [h2'] at h
    omega
  interval_cases x <;> norm_num at h <;> omega