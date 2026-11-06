import Mathlib

theorem number_theory_174543 (x : ℕ) (hx : x = (Nat.digits 10 (1988 - x)).sum) :
    x = 22 := by 
  have h1 : x ≤ 36 := by 
    by_contra h
    push_neg at h
    have h2 : x > 36 := h
    have h3 : (Nat.digits 10 (1988 - x)).sum ≤ 36 := by
      have h4 : 1988 - x ≤ 1988 := by omega
      have h5 : (Nat.digits 10 (1988 - x)).sum ≤ 36 := by 
        interval_cases h6 : 1988 - x <;> norm_num 
      linarith 
    have h6 : (Nat.digits 10 (1988 - x)).sum = x := by linarith [hx]
    linarith [h6, h3, h2]
  interval_cases x <;> norm_num at hx ⊢ <;> omega