import Mathlib

theorem number_theory_323656 (a b c : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (h1 : 3 < a) (h2 : 3 < b) (h3 : 3 < c) (h4 : 2 * a + 5 * b = c) :
    ∃ n, 1 < n ∧ a + b + c ≡ 0 [MOD n] := by
  use 3
  constructor
  · norm_num
  · -- $a + b + c$ is divisible by 3
    have h5 : a + b + c = 3 * (a + 2 * b) := by
      linarith [h4]
    rw [h5]
    simp [Nat.ModEq, Nat.mul_mod, Nat.add_mod]