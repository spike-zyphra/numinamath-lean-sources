import Mathlib

theorem number_theory_168268 {x : ℕ} (hx : x ≠ 0) (h : 196 / x = 169 / x + 3 ∧ 196 % x = 169 % x) :
    169 / x = 18 := by
  have h₁ : 196 / x = 169 / x + 3 := h.left
  have h₂ : 196 % x = 169 % x := h.right
  have h3 : x ≤ 196 := by
    by_contra h4
    push_neg at h4
    have h5 : 196 / x = 0 := by
      rw [Nat.div_eq_zero_iff]
      omega
    have h6 : 169 / x = 0 := by
      rw [Nat.div_eq_zero_iff]
      omega
    omega
  interval_cases x <;> norm_num at h₁ h₂ ⊢
    <;> omega