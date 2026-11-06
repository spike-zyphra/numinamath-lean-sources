import Mathlib

theorem number_theory_449 (L : ℕ) (hL : Nat.Prime L) (hL1 : L ∈ Finset.Icc 10 99) (hL2 : Nat.Prime (L - 2)) (hL3 : ∃ k, k^2 = L - 6) :
    L = 31 := by
  rw [Finset.mem_Icc] at hL1
  rcases hL1 with ⟨hL1a, hL1b⟩
  rcases hL3 with ⟨k, hk⟩
  have h1 : L = k^2 + 6 := by
    omega
  have h2 : k ≥ 2 := by
    nlinarith [h1, hL1a]
  have h3 : k ≤ 9 := by
    nlinarith [h1, hL1b]
  interval_cases k <;> norm_num [h1] at hL hL2 ⊢ <;> try { omega }