import Mathlib

theorem number_theory_275869 (n : ℕ) :
    7 ∣ (2^n + 2^(n+1) + 2^(n+2)) := by
  have h1 : 2^n + 2^(n+1) + 2^(n+2) = 7 * 2^n := by
    ring_nf
  rw [h1]
  exact ⟨2^n, by ring⟩