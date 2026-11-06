import Mathlib

theorem number_theory_237602 (p n : ℕ) (hp : p.Prime) :
    (1 / p : ℚ) = n / 2010 ↔ (p = 2 ∧ n = 1005 ∨ p = 3 ∧ n = 670 ∨ p = 5 ∧ n = 402 ∨ p = 67 ∧ n = 30) := by
  constructor
  · -- Assume (1 / p : ℚ) = n / 2010, prove (p = 2 ∧ n = 1005 ∨ p = 3 ∧ n = 670 ∨ p = 5 ∧ n = 402 ∨ p = 67 ∧ n = 30)
    intro h_eq
    have h1 : (p : ℚ) ≠ 0 := by
      have hp1 : p ≠ 0 := Nat.Prime.ne_zero hp
      exact_mod_cast hp1
    have h2 : (1 : ℚ) * 2010 = (p : ℚ) * (n : ℚ) := by
      field_simp at h_eq ⊢
      linarith
    have h3 : (1 : ℕ) * 2010 = p * n := by
      exact_mod_cast (show (1 * 2010 : ℚ) = (p * n : ℚ) by linarith [h2])
    have h4 : p ∣ 2010 := by
      use n
      all_goals linarith [h3]
    have h5 : p ≤ 2010 := by
      exact Nat.le_of_dvd (by norm_num) h4
    interval_cases p <;> norm_num at hp h4 h3 <;> omega
  · -- Now prove the reverse direction.
    rintro (h | h | h | h)
    · -- Case p = 2 ∧ n = 1005
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case p = 3 ∧ n = 670
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case p = 5 ∧ n = 402
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case p = 67 ∧ n = 30
      rcases h with ⟨rfl, rfl⟩
      norm_num