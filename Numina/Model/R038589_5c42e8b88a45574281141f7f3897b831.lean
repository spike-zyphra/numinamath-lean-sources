import Mathlib

theorem algebra_17080 {r : Set ℕ} (hr : r = {d | d ≥ 10 ∧ d < 100 ∧ 109 ≡ 4 [MOD d]}) :
    (r = {15, 21, 35}) ∧ ∑d∈ {15, 21, 35}, d = 71 := by

  have h1 : r = {15, 21, 35} := by
    ext d
    simp [hr, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume d is in r
      rintro ⟨h10, h100, heq⟩
      interval_cases d <;> norm_num [Nat.ModEq] at heq ⊢
      <;> omega
    · -- Assume d is in {15, 21, 35}
      rintro (rfl | rfl | rfl)
      · constructor
        · norm_num
        constructor
        · norm_num
        · -- Show that 109 ≡ 4 [MOD 15]
          norm_num [Nat.ModEq]
      · constructor
        · norm_num
        constructor
        · norm_num
        · -- Show that 109 ≡ 4 [MOD 21]
          norm_num [Nat.ModEq]
      · constructor
        · norm_num
        constructor
        · norm_num
        · -- Show that 109 ≡ 4 [MOD 35]
          norm_num [Nat.ModEq]
  constructor
  · exact h1
  · -- Show that ∑d∈ {15, 21, 35}, d = 71
    norm_num