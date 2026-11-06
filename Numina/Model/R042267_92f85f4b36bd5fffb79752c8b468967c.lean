import Mathlib

theorem number_theory_22771 {t : ℕ} (ht : 0 < t ∧ t < 23) :
    Odd t ∧ t * (t + 2) ≡ 1 [MOD 23] ↔ t = 17 := by
  constructor
  · -- Assume Odd t ∧ t * (t + 2) ≡ 1 [MOD 23] prove t = 17
    intro h
    rcases h with ⟨ht_odd, ht_mod⟩
    have h1 : t < 23 := ht.right
    have h2 : 0 < t := ht.left
    interval_cases t <;> norm_num [Nat.ModEq] at ht_mod
    <;> try { contradiction }
    <;> try { 
        norm_num [Nat.ModEq] at ht_mod
        all_goals
          try { tauto }
          <;> try { contradiction }
    }
  · -- Assume t = 17 prove Odd t ∧ t * (t + 2) ≡ 1 [MOD 23]
    intro h
    rw [h]
    constructor
    · -- Show 17 is odd
      decide
    · -- Show 17 * (17 + 2) ≡ 1 [MOD 23]
      norm_num [Nat.ModEq]