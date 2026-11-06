import Mathlib

theorem number_theory_2761 {factors : ℕ → ℕ} (hfactors : ∀ n > 0, factors n = ∏ i ∈ Finset.range n, (2 * i + 1)) : (Nat.factorial 2000 / Nat.factorial 1000) / (factors 1000) = 2 ^ 1000 := by
  rw [hfactors 1000 (by norm_num)]
  native_decide