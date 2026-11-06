import Mathlib

theorem number_theory_293532 :
    ∀ N : ℕ, ∃ m n : ℕ,
      m > N ∧ n > N ∧ m ≠ n ∧ IsSquare ((Nat.factorial m) * (Nat.factorial n)) := by
  intro N
  by_cases h : N = 0
  · -- N = 0, so need pair (m, n) s.t. m > 0, n > 0, m ≠ n, and m!n! is square
    rw [h]
    use 4, 3
    all_goals
      native_decide
  · -- N > 0
    have h1 : N > 0 := by
      by_contra h'
      push_neg at h'
      have : N = 0 := by linarith
      contradiction
    have h2 : N ^ 2 + 2 * N > N := by
      nlinarith
    have h3 : N ^ 2 + 2 * N + 1 > N := by
      nlinarith [h1]
    use N ^ 2 + 2 * N, N ^ 2 + 2 * N + 1
    constructor
    · -- Show that m > N
      nlinarith
    constructor
    · -- Show that n > N
      nlinarith
    constructor
    · -- Show that m ≠ n
      show N ^ 2 + 2 * N ≠ N ^ 2 + 2 * N + 1
      omega
    · -- Show that m! * n! is a perfect square
      have h4 : N ^ 2 + 2 * N + 1 = (N + 1) ^ 2 := by
        ring
      have h5 : IsSquare ((Nat.factorial (N ^ 2 + 2 * N)) * (Nat.factorial (N ^ 2 + 2 * N + 1))) := by
        have h6 : (Nat.factorial (N ^ 2 + 2 * N + 1)) = (N ^ 2 + 2 * N + 1) * (Nat.factorial (N ^ 2 + 2 * N)) := by
          simp [Nat.factorial]
          <;> ring
        rw [h6]
        have h7 : IsSquare ((N ^ 2 + 2 * N + 1) * ((Nat.factorial (N ^ 2 + 2 * N)) ^ 2)) := by
          have h8 : IsSquare (N ^ 2 + 2 * N + 1) := by
            use N + 1
            all_goals
              ring
          have h9 : IsSquare ((Nat.factorial (N ^ 2 + 2 * N)) ^ 2) := by
            use (Nat.factorial (N ^ 2 + 2 * N))
            all_goals
              ring
          have h10 : IsSquare ((N ^ 2 + 2 * N + 1) * ((Nat.factorial (N ^ 2 + 2 * N)) ^ 2)) := by
            rcases h8 with ⟨a, ha⟩
            rcases h9 with ⟨b, hb⟩
            use a * b
            rw [ha, hb]
            all_goals
              ring
          exact h10
        have h8 : (Nat.factorial (N ^ 2 + 2 * N)) * ((N ^ 2 + 2 * N + 1) * (Nat.factorial (N ^ 2 + 2 * N))) = (N ^ 2 + 2 * N + 1) * ((Nat.factorial (N ^ 2 + 2 * N)) ^ 2) := by
          ring
        rw [h8] at *
        exact h7
      exact h5