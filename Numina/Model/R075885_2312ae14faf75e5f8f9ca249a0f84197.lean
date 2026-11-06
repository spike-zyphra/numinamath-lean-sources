import Mathlib

theorem algebra_282863 {x : ℕ} (h : x * (x + 1) * (x + 2) = 120) :
    x + (x + 1) + (x + 2) = 15 := by
  have h1 : x ≤ 5 := by
    by_contra h2
    push_neg at h2
    have h2' : x ≥ 6 := by omega
    have h3 : x * (x + 1) * (x + 2) ≥ 336 := by
      have h8 : x ≥ 6 := h2'
      have h9 : x + 1 ≥ 7 := by omega
      have h10 : x + 2 ≥ 8 := by omega
      have h7 : x * (x + 1) * (x + 2) ≥ 6 * 7 * 8 := by
        have h11 : x * (x + 1) ≥ 6 * 7 := by nlinarith
        have h12 : (x * (x + 1)) * (x + 2) ≥ (6 * 7) * 8 := by nlinarith
        nlinarith
      nlinarith
    linarith
  interval_cases x <;> omega