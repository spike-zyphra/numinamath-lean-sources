import Mathlib

theorem algebra_12698 (a x : ℕ) (h : a + x = 24) (hx : x > 0) (hdiv : x % a = 0) :
    a ≤ 12 := by

  by_contra h1
  push_neg at h1

  have h2 : a > 12 := h1
  have h3 : x < 12 := by linarith
  have h5 : a > 0 := by
    by_contra h6
    push_neg at h6
    have : a = 0 := by linarith
    rw [this] at hdiv
    omega

  have h7 : x < a := by
    omega

  have h8 : x = 0 := by
    have h9 : x < a := h7
    have h10 : x % a = x := by
      rw [Nat.mod_eq_of_lt]
      linarith
    rw [hdiv] at h10
    linarith

  linarith