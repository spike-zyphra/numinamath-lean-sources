import Mathlib

theorem algebra_113385 :
    {(a, b) : ℕ × ℕ | |(a : ℤ) - (b : ℤ)| + a * b = 1}.ncard = 3 := by

  have h1 : {(a, b) : ℕ × ℕ | |(a : ℤ) - (b : ℤ)| + a * b = 1} = {(0, 1), (1, 0), (1, 1)} := by
    ext ⟨a, b⟩
    simp
    constructor
    · -- Assume |a - b| + a * b = 1, prove (a, b) ∈ {(0,1), (1,0), (1,1)}
      intro h
      have h2 : (a : ℤ) ≥ 0 := by exact_mod_cast Nat.zero_le a
      have h3 : (b : ℤ) ≥ 0 := by exact_mod_cast Nat.zero_le b

      by_cases h4 : (a : ℤ) ≥ (b : ℤ)
      · -- Case a ≥ b
        have h5 : |(a : ℤ) - (b : ℤ)| = (a : ℤ) - (b : ℤ) := by
          rw [abs_of_nonneg]
          omega
        rw [h5] at h
        have h6 : (a : ℤ) = 1 := by
          nlinarith [h4]
        have ha : a = 1 := by exact_mod_cast h6
        have hb1 : b = 0 ∨ b = 1 := by
          have h4' : (b : ℤ) ≤ (a : ℤ) := by linarith
          have h4'' : (b : ℤ) ≤ 1 := by linarith [h4', h6]
          omega
        rcases hb1 with (hb | hb)
        · -- b = 0
          have hb' : b = 0 := hb
          simp [ha, hb']
        · -- b = 1
          have hb' : b = 1 := hb
          simp [ha, hb']
      · -- Case a < b
        have h5 : |(a : ℤ) - (b : ℤ)| = (b : ℤ) - (a : ℤ) := by
          rw [abs_of_neg]
          omega
          all_goals linarith
        rw [h5] at h
        have h6 : (b : ℤ) = 1 := by
          nlinarith
        have hb : b = 1 := by exact_mod_cast h6
        have h4' : (a : ℤ) < (b : ℤ) := by linarith
        have h4'' : (a : ℤ) < 1 := by linarith [h4', h6]
        have ha1 : a = 0 := by omega
        simp [ha1, hb]
    · -- Show that (0,1), (1,0), (1,1) satisfy the equation
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (0, 1)
        norm_num
      · -- (1, 0)
        norm_num
      · -- (1, 1)
        norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }