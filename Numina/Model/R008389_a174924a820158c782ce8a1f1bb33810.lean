import Mathlib

theorem number_theory_15507 :
    {(r, c) : ℕ × ℕ | r ≥ 2 ∧ c ≥ 2 ∧ r * c = 36}.encard = 7 := by
  have h : {(r, c) : ℕ × ℕ | r ≥ 2 ∧ c ≥ 2 ∧ r * c = 36} = {(2, 18), (3, 12), (4, 9), (6, 6), (9, 4), (12, 3), (18, 2)} := by
    ext ⟨r, c⟩
    simp
    constructor
    · -- Forward: If (r, c) satisfies the conditions, then it's in the set
      rintro ⟨hr, hc, hmul⟩
      have h1 : r ≤ 18 := by nlinarith [hmul, hc]
      interval_cases r <;> omega
    · -- Backward: Each pair in the set satisfies the conditions
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals
        constructor <;> norm_num
  rw [h]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try { tauto }