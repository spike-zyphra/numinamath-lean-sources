import Mathlib

theorem number_theory_127886 (X : Set ℕ) (hpos: ∀n, n∈X → 0<n) (h: ∃ m:ℕ, 1<m ∧ m ∈ X) (hX : ∀ n ∈ X, ∀ m > n, m ∈ X ∨ (n ∣ m)) : ∃ m, ∀ n, m < n → n ∈ X := by
  rcases h with ⟨m, hm1, hm2⟩
  have h3 : m > 1 := by linarith
  have h4 : ∀ (k : ℕ), m + k ∈ X := by
    intro k
    induction k with
    | zero =>
      simpa using hm2
    | succ k ih =>
      have h5 : m + (k + 1) = (m + k) + 1 := by ring
      rw [h5]
      have h6 : (m + k) ∈ X := ih
      have h7 : (m + k + 1) > (m + k) := by linarith
      have h8 : (m + k + 1) ∈ X ∨ ((m + k) ∣ (m + k + 1)) := by
        apply hX (m + k) h6 (m + k + 1) h7
      rcases h8 with (h9 | h10)
      · exact h9
      · 
        have h11 : (m + k) ∣ (m + k + 1) := h10
        have h12 : (m + k) ∣ 1 := by
          have h11' : (m + k) ∣ (m + k + 1 : ℕ) := h11
          have h13 : (m + k) ∣ ((m + k) : ℕ) := by 
            simp
          have h14 : (m + k) ∣ ((m + k + 1 : ℕ) - (m + k)) := by
            apply Nat.dvd_sub'
            · exact h11'
            · exact h13
          have h15 : (m + k + 1 : ℕ) - (m + k) = 1 := by
            omega
          rw [h15] at h14
          exact h14
        have h13 : (m + k) ≤ 1 := by 
          exact Nat.le_of_dvd (by linarith) h12
        have h14 : (m + k) > 1 := by 
          omega
        linarith
  use m - 1
  intro n hn
  have h9 : m ≥ 2 := by omega
  have h10 : m - 1 ≥ 1 := by omega
  have h11 : n > m - 1 := by linarith
  have h12 : n ≥ m := by 
    omega
  have h14 : ∃ k, n = m + k := by 
    refine ⟨n - m, by omega⟩
  rcases h14 with ⟨k, hk⟩
  have h15 : m + k ∈ X := h4 k
  rw [show n = m + k by linarith [hk]] 
  exact h15