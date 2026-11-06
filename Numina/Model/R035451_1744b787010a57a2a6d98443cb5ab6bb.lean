import Mathlib


theorem number_theory_607363 (u : ℕ → ℝ) (h : Function.Periodic u 2022) (h' : Function.Periodic u 5) :
    ∃ c, ∀ n, u n = c := by
  have h1 : ∀ n, u (n + 2022) = u n := by
    intro n
    exact h n
  have h2 : ∀ n, u (n + 5) = u n := by
    intro n
    exact h' n
  have h3 : ∀ n, u (n + 1) = u n := by
    intro n
    have h4 : u (n + 809 * 5) = u n := by
      have h5 : ∀ k, u (n + 5 * k) = u n := by
        intro k
        induction k with
        | zero =>
          simp
        | succ k ih =>
          calc
            u (n + 5 * (k + 1)) = u ( (n + 5 * k) + 5 ) := by ring_nf
            _ = u (n + 5 * k) := by rw [h2]
            _ = u n := by exact ih
      specialize h5 809
      simpa using h5
    have h6 : u (n + 1 + 2 * 2022) = u (n + 1) := by
      have h7 : u ( (n + 1) + 2022 ) = u (n + 1) := by
        apply h1
      calc
        u (n + 1 + 2 * 2022) = u ( (n + 1 + 2022) + 2022 ) := by ring_nf
        _ = u (n + 1 + 2022) := by rw [h1]
        _ = u (n + 1) := by rw [h1]
    have h8 : n + 809 * 5 = n + 1 + 2 * 2022 := by
      omega
    have h9 : u (n + 1 + 2 * 2022) = u n := by
      rw [show n + 809 * 5 = n + 1 + 2 * 2022 by omega] at h4
      linarith
    linarith [h9, h6]
  use u 0
  intro n
  induction n with
  | zero =>
    simp
  | succ k ih =>
    have h10 : u (k + 1) = u k := h3 k
    rw [h10]
    exact ih