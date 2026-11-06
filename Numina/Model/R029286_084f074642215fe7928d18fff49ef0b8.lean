import Mathlib

theorem algebra_97634 :
    {(m, n) : ℕ × ℕ | m > 0 ∧ n > 0 ∧ (4 / m : ℝ) + (2 / n : ℝ) = 1}.ncard = 4 := by
  have h1 : {(m, n) : ℕ × ℕ | m > 0 ∧ n > 0 ∧ (4 / m : ℝ) + (2 / n : ℝ) = 1} = {(5, 10), (6, 6), (8, 4), (12, 3)} := by
    ext ⟨m, n⟩
    simp
    constructor
    · -- Assume (m, n) is in the set
      rintro ⟨hm, hn, h⟩
      have h2 : (m : ℝ) > 0 := by exact_mod_cast hm
      have h3 : (n : ℝ) > 0 := by exact_mod_cast hn
      have h4 : (m : ℝ) * (n : ℝ) = 2 * (m : ℝ) + 4 * (n : ℝ) := by
        field_simp at h
        linarith
      have h5 : (m : ℕ) * (n : ℕ) = 2 * (m : ℕ) + 4 * (n : ℕ) := by
        exact_mod_cast h4
      have h6 : m ≤ 12 := by
        by_contra h
        push_neg at h
        have h7 : n ≤ 2 := by
          nlinarith [show m ≥ 13 from by linarith, show n ≥ 1 from by linarith, h5]
        interval_cases n <;> try { 
          omega
        }
      interval_cases m <;> try { 
        omega
      }
    · -- Show the four pairs satisfy the equation
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- (5, 10)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- (6, 6)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- (8, 4)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- (12, 3)
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }