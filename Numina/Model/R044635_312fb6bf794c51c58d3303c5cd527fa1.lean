import Mathlib

theorem number_theory_130432 (m n : ℕ) :
    m ≠ 0 ∧ n ≠ 0 ∧ (3 / m : ℚ) + (5 / n : ℚ) = 1 ↔
    (m = 4 ∧ n = 20) ∨ (m = 6 ∧ n = 10) ∨ (m = 8 ∧ n = 8) ∨ (m = 18 ∧ n = 6) := by
  constructor
  · -- Assume m ≠ 0 ∧ n ≠ 0 ∧ (3 / m : ℚ) + (5 / n : ℚ) = 1, prove (m = 4 ∧ n = 20) ∨ (m = 6 ∧ n = 10) ∨ (m = 8 ∧ n = 8) ∨ (m = 18 ∧ n = 6)
    rintro ⟨hm, hn, heq⟩
    have eq1 : (3 : ℚ) / m + (5 : ℚ) / n = (1 : ℚ) := by
      linarith
    have eq2 : m > 0 := by
      by_contra h
      push_neg at h
      have : m = 0 := by linarith
      contradiction
    have eq3 : n > 0 := by
      by_contra h
      push_neg at h
      have : n = 0 := by linarith 
      contradiction
    have eq4 : (3 * (n : ℚ) + 5 * (m : ℚ)) = (m : ℚ) * (n : ℚ) := by
      have h1 : (m : ℚ) ≠ 0 := by
        have h2 : (m : ℚ) > (0 : ℚ) := by
          exact_mod_cast (show m > 0 by linarith)
        linarith
      have h2 : (n : ℚ) ≠ 0 := by
        have h3 : (n : ℚ) > (0 : ℚ) := by
          exact_mod_cast (show n > 0 by linarith)
        linarith
      field_simp [h1, h2] at eq1 ⊢
      nlinarith
    have eq5 : 3 * (n : ℕ) + 5 * (m : ℕ) = (m : ℕ) * (n : ℕ) := by
      exact_mod_cast (eq4)
    have h1 : m ≤ 20 := by
      by_contra h 
      push_neg at h 
      have h2 : n ≤ 5 := by
        nlinarith [show m > 0 from by linarith, show n > 0 from by linarith, eq5]
      interval_cases n <;> try { 
        omega 
      }
    interval_cases m <;> omega
  · -- Assume (m = 4 ∧ n = 20) ∨ (m = 6 ∧ n = 10) ∨ (m = 8 ∧ n = 8) ∨ (m = 18 ∧ n = 6), prove m ≠ 0 ∧ n ≠ 0 ∧ (3 / m : ℚ) + (5 / n : ℚ) = 1
    rintro (h | h | h | h)
    · -- First solution 
      rcases h with ⟨rfl, rfl⟩
      constructor
      · norm_num 
      constructor
      · norm_num
      · norm_num
    · -- Second solution 
      rcases h with ⟨rfl, rfl⟩
      constructor
      · norm_num 
      constructor
      · norm_num
      · norm_num
    · -- Third solution 
      rcases h with ⟨rfl, rfl⟩ 
      constructor
      · norm_num 
      constructor
      · norm_num 
      · norm_num
    · -- Fourth solution 
      rcases h with ⟨rfl, rfl⟩ 
      constructor
      · norm_num 
      constructor
      · norm_num 
      · norm_num