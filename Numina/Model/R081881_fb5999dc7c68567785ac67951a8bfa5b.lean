import Mathlib

theorem number_theory_291358 (x : ℕ) (hx : x > 0) (h : x = (Nat.digits 10 (1893 - x)).sum) :
    x = 24 := by
  have h2 : x ≤ 1893 := by
    by_contra h3
    push_neg at h3
    have h4 : 1893 - x = 0 := by
      omega
    rw [h4] at h
    norm_num at h
    linarith
  interval_cases x <;> norm_num at h ⊢ <;> all_goals omega