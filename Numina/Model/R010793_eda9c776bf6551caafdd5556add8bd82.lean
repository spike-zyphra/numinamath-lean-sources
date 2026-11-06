import Mathlib

theorem algebra_10852 (a : ℕ → ℕ) (ha1 : a 1 = 1) (han : ∀ n, 1 ≤ n → a (n + 1) = a n + 3) :
    a 100 = 298 := by
  have h : ∀ n, a (n + 1) = 1 + 3 * n := by
    intro n
    induction n with
    | zero =>
      simp [ha1]
    | succ n ih =>
      calc
        a (n + 1 + 1) = a (n + 1) + 3 := by
          apply han
          omega
        _ = (1 + 3 * n) + 3 := by
          rw [ih]
        _ = 1 + 3 * (n + 1) := by
          ring_nf
          <;> omega
  have h99 := h 99
  norm_num at h99 ⊢
  exact h99