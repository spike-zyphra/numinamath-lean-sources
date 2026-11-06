import Mathlib

open Finset

theorem number_theory_260579 {f : (ℕ × ℕ) → (ℕ × ℕ)}
    (hf : ∀ s, ∃ m n, s = (m, n) ∧ Nat.Coprime m n ∧ Even n ∧ m < n ∧
      ∃ k n0, n = 2 ^ k * n0 ∧ Odd n0 ∧ f s = (n0, m + n - n0)) :
    (∀ s, ∃ t, 0 < t ∧ t ≤ (s.1 + s.2 + 1) / 4 ∧ f^[t] s = s) ∧
    (∀ m n, Nat.Prime (m + n) → ¬∃ k, k ≤ m + n - 2 ∧ (2 ^ k - 1) ∣ n →
      IsLeast {t | 0 < t ∧ t ≤ (m + n + 1) / 4 ∧ f^[t] (m, n) = (m, n)} ((m + n + 1) / 4)) := by
  -- Let's pick s = (0, 0) and derive a contradiction
  have h1 := hf (0, 0)
  rcases h1 with ⟨m, n, h_eq, h_coprime, h_even, h_lt, k, n0, h_eq_n, h_odd, h_f⟩
  have h1 : m = 0 := by 
    simp [Prod.ext_iff] at h_eq 
    omega 
  have h2 : n = 0 := by 
    simp [Prod.ext_iff] at h_eq 
    omega 
  simp [h1, h2] at h_lt