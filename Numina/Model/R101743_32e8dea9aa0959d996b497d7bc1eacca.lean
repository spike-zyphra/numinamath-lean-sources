import Mathlib

theorem number_theory_239231 (n : ℕ) (h : Odd n) :
    21 ∣ 2^n + 2^(n+2) + 2^(n+4) := by

  have h1 : 2^n + 2^(n+2) + 2^(n+4) = 2^n * 21 := by
    ring_nf

  rw [h1]
  exact ⟨2^n, by ring⟩