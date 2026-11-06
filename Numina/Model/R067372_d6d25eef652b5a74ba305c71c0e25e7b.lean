import Mathlib

theorem algebra_165813 :
    {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a + a * b + a * b * c = 11}.ncard = 3 := by
  have h1 : {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a + a * b + a * b * c = 11} = {(1, 1, 9), (1, 2, 4), (1, 5, 1)} := by
    ext ⟨a, b, c⟩
    simp
    constructor
    · -- First, we show that if (a, b, c) is in the set, then it must be one of the three given triples
      rintro ⟨ha, hb, hc, heq⟩
      have h2 : a ∣ 11 := by
        use 1 + b + b * c
        all_goals nlinarith
      have h3 : a = 1 ∨ a = 11 := by
        have h4 : a ≤ 11 := by
          exact Nat.le_of_dvd (by norm_num) h2
        interval_cases a <;> try { tauto }
        <;> norm_num at h2 <;> tauto
      rcases h3 with h3 | h3
      · -- Case where a = 1
        rw [h3] at heq
        have h4 : b ≤ 10 := by
          nlinarith [show b > 0 by exact hb, show c > 0 by exact hc]
        interval_cases b <;> omega
      · -- Case where a = 11
        rw [h3] at heq
        have h4 : b > 0 := hb
        have h5 : c > 0 := hc
        nlinarith [show b > 0 by exact hb, show c > 0 by exact hc]
    · -- Show that the three given triples are indeed in the set
      rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
      all_goals
        simp
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { tauto }
  all_goals try { tauto }
  all_goals try { try { native_decide } }
  <;> try { try { native_decide } }