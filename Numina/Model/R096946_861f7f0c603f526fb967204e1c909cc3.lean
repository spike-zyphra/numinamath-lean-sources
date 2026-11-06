import Mathlib

theorem number_theory_14 {m n : ℕ} (hm : m = 2^2 * 3) (hn : n = 2^3 * 3) : Nat.lcm m n = 24 := by
  rw [hm, hn]
  rfl