import Mathlib

theorem number_theory_16151 : IsLeast {n : ℕ | 0 < n ∧ (531 * n ≡ 1067 * n [MOD 24])} 3 := by
  constructor
  · -- Show 3 is in the set.
    constructor
    · norm_num
    · -- Show that $531 \cdot 3 \equiv 1067 \cdot 3 \pmod{24}$.
      norm_num [Nat.ModEq]
  · -- Show that 3 is the smallest.
    intro n hn
    have h1 : 0 < n := hn.1
    have h2 : 531 * n ≡ 1067 * n [MOD 24] := hn.2
    norm_num [Nat.ModEq] at h2
    omega