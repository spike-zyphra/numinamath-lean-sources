import Mathlib

theorem algebra_119285 : IsGreatest {x | ∀ n ∈ Finset.Icc 1983 1992, x ∣ (n^3 + 3 * n^2 + 2 * n)} 6 := by
  constructor
  · -- Show that 6 is in the set.
    intro n hn
    have h1 : 1983 ≤ n := by
      have h2 : n ∈ Finset.Icc (1983 : ℕ) (1992 : ℕ) := hn
      simp at h2 ⊢
      omega
    have h2 : n ≤ 1992 := by
      have h3 : n ∈ Finset.Icc (1983 : ℕ) (1992 : ℕ) := hn
      simp at h3 ⊢
      omega
    have h6 : 6 ∣ (n^3 + 3 * n^2 + 2 * n) := by
      interval_cases n <;> norm_num 
    exact h6
  · -- Show that 6 is greatest.
    intro x hx
    have h6 : ∀ n ∈ Finset.Icc (1983 : ℕ) (1992 : ℕ), x ∣ (n^3 + 3 * n^2 + 2 * n) := hx
    have h1 := h6 1983 (by simp)
    have h2 := h6 1984 (by simp)
    have h3 := h6 1985 (by simp)
    have h4 := h6 1986 (by simp)
    have h5 := h6 1987 (by simp)
    have h6' := h6 1988 (by simp)
    have h7 := h6 1989 (by simp)
    have h8 := h6 1990 (by simp)
    have h9 := h6 1991 (by simp)
    have h10 := h6 1992 (by simp)
    -- Show that x ∣ 6, and then conclude that x ≤ 6
    have h11 : x ∣ 6 := by 
      exact Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd h1 h2) h3) h4) h5) h6') h7) h8) h9) h10
    have hx : x ≤ 6 := by 
      exact Nat.le_of_dvd (by norm_num) h11
    linarith