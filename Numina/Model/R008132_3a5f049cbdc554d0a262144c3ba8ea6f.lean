import Mathlib

theorem number_theory_19174 : {x | x ∣ 252 ∧ Even x}.encard = 12 := by
  have h1 : {x | x ∣ 252 ∧ Even x} = {2, 4, 6, 12, 14, 18, 28, 42, 36, 84, 126, 252} := by
    ext n
    simp [Nat.even_iff]
    constructor
    · -- Proof of the forward direction: If n divides 252 and is even, then n is in the set.
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : n ≤ 252 := by exact Nat.le_of_dvd (by norm_num) h1
      interval_cases n <;> tauto
    · -- Proof of the reverse direction: If n is in the set, then n divides 252 and is even.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · decide
      · constructor
        · norm_num
        · decide
      · constructor
        · norm_num
        · decide
      · constructor
        · norm_num
        · decide
      · constructor
        · norm_num
        · decide
      · constructor
        · norm_num
        · decide
      · constructor
        · norm_num
        · decide
      · constructor
        · norm_num
        · decide
      · constructor
        · norm_num
        · decide
      · constructor
        · norm_num
        · decide
      · constructor
        · norm_num
        · decide
      · constructor
        · norm_num
        · decide
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try { rfl }