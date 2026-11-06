import Mathlib

theorem number_theory_22775 {n : ℕ} (hn : n ∈ Finset.range 18) :
    n ≡ 142857 [MOD 18] ↔ n = 9 := by
  rw [Finset.mem_range] at hn
  simp [Nat.ModEq] at *
  constructor
  · -- Forward direction: if n ≡ 142857 [MOD 18], then n = 9
    intro h
    omega
  · -- Backward direction: if n = 9, then n ≡ 142857 [MOD 18]
    intro h
    subst n
    all_goals norm_num