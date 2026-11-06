import Mathlib

theorem number_theory_262160 :
    Set.ncard {p : ℤ × ℤ | p.1 ≥ -9 ∧ p.2 ≥ -2 ∧ p.1 ≤ 6 ∧ p.2 ≤ 8 ∧ ∃ k : ℚ, p.1 = -9 * k + 6 * (1 - k) ∧ p.2 = -2 * k + 8 * (1 - k)} = 6 := by
  have h1 : {p : ℤ × ℤ | p.1 ≥ -9 ∧ p.2 ≥ -2 ∧ p.1 ≤ 6 ∧ p.2 ≤ 8 ∧ ∃ k : ℚ, p.1 = -9 * k + 6 * (1 - k) ∧ p.2 = -2 * k + 8 * (1 - k)} = {(-9, -2), (-6, 0), (-3, 2), (0, 4), (3, 6), (6, 8)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Forward
      rintro ⟨hx1, hy1, hx2, hy2, ⟨k, h1, h2⟩⟩
      have h1' : (x : ℚ) = -9 * k + 6 * (1 - k) := by
        simpa using h1
      have h2' : (y : ℚ) = -2 * k + 8 * (1 - k) := by
        simpa using h2
      have eq1 : (x : ℚ) = 6 - 15 * k := by
        linarith
      have eq2 : (y : ℚ) = 8 - 10 * k := by
        linarith
      have h3 : 3 * y - 2 * x = 12 := by
        have h3' : (3 * (y : ℚ) - 2 * (x : ℚ)) = (12 : ℚ) := by
          rw [eq1, eq2]
          linarith
        exact_mod_cast h3'
      interval_cases x <;> omega
    · -- Backward
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (-9, -2)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · use (1 : ℚ)
          all_goals norm_num
      · -- (-6, 0)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · use (0.8 : ℚ)
          constructor
          · norm_num
          · norm_num
      · -- (-3, 2)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · use (0.6 : ℚ)
          constructor
          · norm_num
          · norm_num
      · -- (0, 4)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · use (0.4 : ℚ)
          constructor
          · norm_num
          · norm_num
      · -- (3, 6)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · use (0.2 : ℚ)
          constructor
          · norm_num
          · norm_num
      · -- (6, 8)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · use (0 : ℚ)
          constructor
          · norm_num
          · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { 
    native_decide
  }
  <;> try { 
    omega
  }