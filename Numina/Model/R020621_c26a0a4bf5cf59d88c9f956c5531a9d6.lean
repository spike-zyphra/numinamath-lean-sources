import Mathlib

def fib (n : ℕ) : ℕ := match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

theorem number_theory_116101 (n : ℕ) :
    Even (fib n) ↔ 3 ∣ n := by
  constructor
  · -- Assume Even (fib n), prove 3 ∣ n
    intro h
    have h1 : ∀ (k : ℕ), fib (3 * k) % 2 = 0 := by
      intro k
      induction k with
      | zero =>
        simp [fib]
      | succ k ih =>
        have h2 : fib (3 * (k + 1)) = fib (3 * k + 3) := by
          ring_nf
        rw [h2]
        have h3 : fib (3 * k + 3) = fib (3 * k + 1) + fib (3 * k + 2) := by
          simp [fib]
          all_goals
            ring_nf
        rw [h3]
        have h4 : fib (3 * k + 1) % 2 = 1 := by
          have h2 : ∀ (k : ℕ), fib (3 * k + 1) % 2 = 1 := by
            intro k
            induction k with
            | zero =>
              simp [fib]
            | succ k ih =>
              have h9 : fib (3 * (k + 1) + 1) = fib (3 * k + 1 + 3) := by
                ring_nf
              rw [h9]
              simp [fib] at ih ⊢
              all_goals
                omega
          specialize h2 k
          simpa using h2
        have h5 : fib (3 * k + 2) % 2 = 1 := by
          have h3 : ∀ (k : ℕ), fib (3 * k + 2) % 2 = 1 := by
            intro k
            induction k with
            | zero =>
              simp [fib]
            | succ k ih =>
              have h9 : fib (3 * (k + 1) + 2) = fib (3 * k + 2 + 3) := by
                ring_nf
              rw [h9]
              simp [fib] at ih ⊢
              all_goals
                omega
          specialize h3 k
          simpa using h3
        omega
    have h4 : n % 3 = 0 := by
      by_contra h4
      push_neg at h4
      have h5 : n % 3 = 1 ∨ n % 3 = 2 := by
        omega
      rcases h5 with (h5 | h5)
      · -- n % 3 = 1
        have h6 : ∃ k, n = 3 * k + 1 := by
          have : n % 3 = 1 := h5
          refine' ⟨(n - 1) / 3, by omega⟩
        rcases h6 with ⟨k, hk⟩
        have h7 : fib (3 * k + 1) % 2 = 1 := by
          have h2 : ∀ (k : ℕ), fib (3 * k + 1) % 2 = 1 := by
            intro k
            induction k with
            | zero =>
              simp [fib]
            | succ k ih =>
              have h9 : fib (3 * (k + 1) + 1) = fib (3 * k + 1 + 3) := by
                ring_nf
              rw [h9]
              simp [fib] at ih ⊢
              all_goals
                omega
          specialize h2 k
          simpa using h2
        have h9 : fib n % 2 = 0 := by
          obtain ⟨m, hm⟩ := h
          omega
        rw [show n = 3 * k + 1 by omega] at h9
        omega
      · -- n % 3 = 2
        have h6 : ∃ k, n = 3 * k + 2 := by
          have : n % 3 = 2 := h5
          refine' ⟨(n - 2) / 3, by omega⟩
        rcases h6 with ⟨k, hk⟩
        have h7 : fib (3 * k + 2) % 2 = 1 := by
          have h3 : ∀ (k : ℕ), fib (3 * k + 2) % 2 = 1 := by
            intro k
            induction k with
            | zero =>
              simp [fib]
            | succ k ih =>
              have h9 : fib (3 * (k + 1) + 2) = fib (3 * k + 2 + 3) := by
                ring_nf
              rw [h9]
              simp [fib] at ih ⊢
              all_goals
                omega
          specialize h3 k
          simpa using h3
        have h9 : fib n % 2 = 0 := by
          obtain ⟨m, hm⟩ := h
          omega
        rw [show n = 3 * k + 2 by omega] at h9
        omega
    have : 3 ∣ n := by
      omega
    assumption
  · -- Assume 3 ∣ n, prove Even (fib n)
    intro h
    rcases h with ⟨k, hk⟩
    have h1 : ∀ (k : ℕ), fib (3 * k) % 2 = 0 := by
      intro k
      induction k with
      | zero =>
        simp [fib]
      | succ k ih =>
        have h2 : fib (3 * (k + 1)) = fib (3 * k + 3) := by
          ring_nf
        rw [h2]
        have h3 : fib (3 * k + 3) = fib (3 * k + 1) + fib (3 * k + 2) := by
          simp [fib]
          all_goals
            ring_nf
        rw [h3]
        have h4 : fib (3 * k + 1) % 2 = 1 := by
          have h2 : ∀ (k : ℕ), fib (3 * k + 1) % 2 = 1 := by
            intro k
            induction k with
            | zero =>
              simp [fib]
            | succ k ih =>
              have h9 : fib (3 * (k + 1) + 1) = fib (3 * k + 1 + 3) := by
                ring_nf
              rw [h9]
              simp [fib] at ih ⊢
              all_goals
                omega
          specialize h2 k
          simpa using h2
        have h5 : fib (3 * k + 2) % 2 = 1 := by
          have h3 : ∀ (k : ℕ), fib (3 * k + 2) % 2 = 1 := by
            intro k
            induction k with
            | zero =>
              simp [fib]
            | succ k ih =>
              have h9 : fib (3 * (k + 1) + 2) = fib (3 * k + 2 + 3) := by
                ring_nf
              rw [h9]
              simp [fib] at ih ⊢
              all_goals
                omega
          specialize h3 k
          simpa using h3
        omega
    have h2 : fib (3 * k) % 2 = 0 := h1 k
    have h3 : fib n % 2 = 0 := by
      rw [show n = 3 * k by
        omega
      ]
      exact h1 k
    have : Even (fib n) := by
      refine' ⟨fib n / 2, by omega⟩
    assumption