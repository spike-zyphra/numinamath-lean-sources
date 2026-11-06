import Mathlib

theorem inequalities_74834 {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : m * n % (m + n) = 0) : m + n ≤ n ^ 2 := by
  by_contra h1
  push_neg at h1
  have h7 : m + n > n ^ 2 := h1
  have h6 : m + n ∣ m * n := by 
    exact Nat.dvd_of_mod_eq_zero h
  rcases h6 with ⟨k, hk⟩
  have h9 : k < n := by
    nlinarith [show m * n = (m + n) * k from by linarith [hk], h7, show 0 < m by linarith, show 0 < n by linarith]
  nlinarith [show m * n = (m + n) * k from by linarith [hk  ], h7, show 0 < m by linarith, show 0 < n by linarith, h9, mul_pos hm hn]