import Mathlib

theorem algebra_96450 {x y : ℕ} (hx : 0 < y) (hy : y < x) (h : x + y + x * y = 80) : x = 26 := by
  have h1 : x ≤ 39 := by
    by_contra h1
    push_neg at h1
    have h2 : y ≤ 1 := by
      nlinarith
    have h3 : y = 1 := by
      omega
    rw [h3] at h
    nlinarith
  have h2 : y ≤ 39 := by
    by_contra h2
    push_neg at h2
    have h4 : x ≤ 1 := by
      nlinarith
    have h5 : x = 1 := by
      omega
    rw [h5] at h
    nlinarith
  interval_cases y <;> interval_cases x <;> omega