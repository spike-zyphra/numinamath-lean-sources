import Mathlib

theorem number_theory_141769 (n : ℕ) (hn : 0 < n) : 3 ∣ 2 * n + 1 ↔ n ≡ 1 [MOD 3] := by
  simp [Nat.ModEq]
  constructor
  · -- Assume 3 ∣ 2 * n + 1 and prove n ≡ 1 [MOD 3]
    intro h
    have h1 : n % 3 = 1 := by
      omega
    exact h1
  · -- Assume n ≡ 1 [MOD 3] and prove 3 ∣ 2 * n + 1
    intro h
    have h1 : n % 3 = 1 := h
    omega