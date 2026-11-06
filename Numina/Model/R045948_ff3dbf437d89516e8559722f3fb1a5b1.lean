import Mathlib

theorem number_theory_607433 :
    ∀ N : ℕ, ∃ m n : ℕ,
      m > N ∧ n > N ∧ m ≠ n ∧ IsSquare (Nat.factorial m * Nat.factorial n) :=
by
  intro N
  have h1 : ∃ k : ℕ, k ^ 2 > N + 1 := by
    by_contra h
    push_neg at h
    have h2 : ∀ k : ℕ, k ^ 2 ≤ N + 1 := by
      intro k
      specialize h k
      linarith
    have h3 : (N + 2) ^ 2 > N + 1 := by
      nlinarith [sq_nonneg (N + 2 : ℕ)]
    have h4 : (N + 2) ^ 2 ≤ N + 1 := by
      apply h2 (N + 2)
    linarith
  rcases h1 with ⟨k, hk⟩
  have h2 : k ^ 2 > N + 1 := hk
  have h3 : k ^ 2 ≥ N + 2 := by
    omega
  have h4 : k ≥ 1 := by
    by_contra h
    push_neg at h
    have h0 : k = 0 := by
      omega
    rw [h0] at h2
    nlinarith
  have h5 : k ^ 2 ≥ 1 := by
    nlinarith [sq_pos_of_pos (show k > 0 by omega)]
  set m := k ^ 2 - 1 with hm
  set n := k ^ 2 with hn
  use m, n
  constructor
  · -- m > N
    omega
  constructor
  · -- n > N
    omega
  constructor
  · -- m ≠ n
    omega
  · -- IsSquare (Nat.factorial m * Nat.factorial n)
    have h7 : Nat.factorial m * Nat.factorial n = (Nat.factorial (k ^ 2 - 1) * k) ^ 2 := by
      have h9 : Nat.factorial (k ^ 2) = k ^ 2 * Nat.factorial (k ^ 2 - 1) := by
        have h2 : k ^ 2 ≥ 1 := h5
        rw [show k ^ 2 = (k ^ 2 - 1) + 1 by
          omega
        ]
        simp [Nat.factorial]
        all_goals
          ring
      have h90 : Nat.factorial m * Nat.factorial n = (Nat.factorial (k ^ 2 - 1) ) ^ 2 * k ^ 2 := by
        rw [show n = k ^ 2 by rfl]
        rw [show m = k ^ 2 - 1 by rfl]
        rw [h9]
        ring
      have h91 : (Nat.factorial (k ^ 2 - 1) * k) ^ 2 = (Nat.factorial (k ^ 2 - 1) ) ^ 2 * k ^ 2 := by
        ring
      nlinarith [h90, h91]
    rw [h7]
    exact ⟨Nat.factorial (k ^ 2 - 1) * k, by ring⟩