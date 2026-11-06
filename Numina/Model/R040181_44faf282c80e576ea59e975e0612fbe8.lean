import Mathlib

theorem number_theory_319463 {b : ℕ} (hb : b > 1) (h : (Nat.digits b 1999).length = 3)
    (h1 : (Nat.digits b 1999).headI + (Nat.digits b 1999).tail.headI + (Nat.digits b 1999).tail.tail.headI = 1 + 9 + 9 + 9) :
    b = 28 := by
  have h2 : b ≤ 1999 := by
    by_contra h3
    push_neg at h3
    have h3 : b > 1999 := h3
    have h4 : (Nat.digits b 1999).length = 1 := by
      simp [h3]
      all_goals
        omega
    omega
  interval_cases b <;> norm_num at h h1 ⊢ <;> all_goals try { tauto }
  <;> omega