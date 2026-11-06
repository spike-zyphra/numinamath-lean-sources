import Mathlib

theorem number_theory_177262 (x : ℕ) (hx : x > 0) (h1 : (Nat.digits 10 x).sum * 3 = x) (h2 : (Nat.digits 10 x).sum ^ 2 = 3 * x) :
    x = 27 := by
  have h4 : (Nat.digits 10 x).sum > 0 := by 
    by_contra h
    push_neg at h
    have h5 : (Nat.digits 10 x).sum = 0 := by linarith
    have h6 : x = 0 := by 
      have : (Nat.digits 10 x).sum * 3 = x := h1
      rw [h5] at this
      linarith
    linarith

  have h5 : (Nat.digits 10 x).sum = 9 := by
    nlinarith [h1, h2, h4]
  calc
    x = (Nat.digits 10 x).sum * 3 := by linarith [h1]
    _ = 9 * 3 := by rw [h5]
    _ = 27 := by norm_num