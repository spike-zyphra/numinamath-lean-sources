import Mathlib

theorem algebra_288393 {a b c d : ℕ} (ha : a = 15) (hb : b > 0) (hc : c = 10)
    (hd : d > 0) (h : a^2 = b^2 + c^2 + d^2) :
    b + d = 13 ∨ b + d = 15 := by 
  rw [ha, hc] at h
  have h_eq : 15^2 = b^2 + 10^2 + d^2 := h
  have h_eq_simp : 225 = b^2 + 100 + d^2 := by 
    norm_num at h_eq ⊢ 
    exact h_eq
  have h_eq_final : b^2 + d^2 = 125 := by
    linarith [h_eq_simp]
  have h1 : b ≤ 11 := by
    nlinarith [sq_nonneg (b : ℕ), sq_nonneg (d : ℕ)
      ]
  have h2 : d ≤ 11 := by
    nlinarith [sq_nonneg (b : ℕ), sq_nonneg (d : ℕ)
      ]
  interval_cases b <;> interval_cases d <;> norm_num at h_eq_final ⊢ <;> omega