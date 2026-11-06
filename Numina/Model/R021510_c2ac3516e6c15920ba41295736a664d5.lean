import Mathlib

theorem number_theory_280386 :
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧ ∃ a b : ℕ, a^2 + b^2 = n ∧ ¬∃ c d : ℕ, c^2 + d^2 = n - 1 ∧
      ¬∃ e f : ℕ, e^2 + f^2 = n + 1 := by
  intro N
  use (N + 1) ^ 2
  constructor
  · -- Show that n > N.
    nlinarith [sq_pos_of_pos (show 0 < N + 1 by omega)]
  · -- Show the existence of a and b.
    use (N + 1)
    use 0
    constructor
    · -- Show that a^2 + b^2 = n.
      simp [Nat.pow_two]
      <;> ring
    · -- Prove the negation part.
      intro h
      rcases h with ⟨c, d, h1, h2⟩
      have h3 : ∃ e f : ℕ, e^2 + f^2 = (N + 1) ^ 2 + 1 := by
        use 1
        use N + 1
        all_goals
          ring_nf
      exfalso
      have h4 : ∃ e f : ℕ, e^2 + f^2 = (N + 1) ^ 2 + 1 := h3
      tauto