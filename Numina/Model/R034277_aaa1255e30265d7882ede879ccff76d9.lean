import Mathlib

theorem number_theory_181397 {x y : ℕ} (h : x + y ≠ 0) (h1 : x - y ≠ 0) (h2 : x * y ≠ 0)
    (h3 : (x + y) * 18 = (x - y) * 5) (h4 : (x + y) * 5 = x * y) :
    x = 96 ∧ y = 18 := by
  have h5 : x > y := by
    by_contra h5
    push_neg at h5
    have h6 : x ≤ y := by linarith
    have h7 : x - y = 0 := by
      omega
    contradiction
  have h6 : x - y > 0 := by
    omega
  have h7 : (x + y) * 18 > (x - y) * 5 := by
    have h5 : x > y := h5
    have h8 : x + y > x - y := by
      omega
    nlinarith
  nlinarith