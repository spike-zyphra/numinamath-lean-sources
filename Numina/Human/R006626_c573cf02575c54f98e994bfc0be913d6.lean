import Mathlib

/-Let $k$ be a non-negative integer. Let $n = 10k + 9$. Show that $n^n \pmod{10} = 9$.-/
theorem number_theory_639403 {n k : ℕ} (hn : n = 10 * k + 9) : n ^ n ≡ 9 [MOD 10] := by
  rw [Nat.ModEq, hn, Nat.pow_mod, Nat.add_mod]
  simp only [Nat.mul_mod_right, Nat.mod_succ, zero_add]
  rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  simp
