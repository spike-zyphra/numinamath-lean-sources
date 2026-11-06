import Mathlib

theorem number_theory_123107 (n : ℤ) :
    ∃ m : ℤ, (n^5 / 5 + n^3 / 3 + 7 * n / 15 : ℚ) = m := by
  have h1 : (n ^ 5 : ℚ) / 5 + (n ^ 3 : ℚ) / 3 + (7 * (n : ℚ) / 15) = (3 * (n^5 : ℚ) + 5 * (n^3 : ℚ) + 7 * (n : ℚ)) / 15 := by
    field_simp
    <;> ring
  have h2 : ((3 * n ^ 5 + 5 * n ^ 3 + 7 * n) : ℤ) % 15 = 0 := by
    have h2a : (3 * n ^ 5 + 5 * n ^ 3 + 7 * n) % 3 = 0 := by
      have h3a : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h3a with (h3a | h3a | h3a)
      all_goals
        simp [h3a, Int.add_emod, Int.mul_emod, pow_succ, Int.sub_emod]
    have h2b : (3 * n ^ 5 + 5 * n ^ 3 + 7 * n) % 5 = 0 := by
      have h3b : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
      rcases h3b with (h3b | h3b | h3b | h3b | h3b)
      all_goals
        simp [h3b, Int.add_emod, Int.mul_emod, pow_succ, Int.sub_emod]
    omega
  use (3 * n ^ 5 + 5 * n ^ 3 + 7 * n) / 15
  rw [h1]
  have h4 : ((3 * n ^ 5 + 5 * n ^ 3 + 7 * n) : ℤ) % 15 = 0 := h2
  field_simp at *
  <;> norm_cast
  all_goals norm_num at h4 ⊢
  all_goals omega