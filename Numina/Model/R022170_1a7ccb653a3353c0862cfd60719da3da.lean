import Mathlib

theorem number_theory_280661 (a : ℕ → ℕ) (ha : a 0 = 7)
    (h : ∀ n, a n + a (n + 1) + a (n + 2) + a (n + 3) = 30) :
    a 1992 = 7 := by
  have h1 : ∀ n, a (n + 4) = a n := by
    intro n
    have eq1 := h n
    have eq2 := h (n + 1)
    simp [show n + 1 + 1 = n + 2 by omega, show n + 2 + 1 = n + 3 by omega, show n + 3 + 1 = n + 4 by omega] at eq1 eq2 ⊢
    omega
  have h2 : ∀ k, a (4 * k) = a 0 := by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      calc
        a (4 * (k + 1)) = a (4 * k + 4) := by ring_nf
        _ = a (4 * k) := by rw [h1 (4 * k)]
        _ = a 0 := by rw [ih]
  have h3 : a 1992 = a 0 := by
    specialize h2 498
    norm_num at h2 ⊢
    exact h2
  rw [h3, ha]