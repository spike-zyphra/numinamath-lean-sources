import Mathlib

open Real
open scoped BigOperators

theorem algebra_265468 {V : ℕ → ℝ}
  (hV : ∀ n, V n = (n^3 - 10 * n^2 + 17 * n - 4) / (n^2 - 10 * n + 18)) :
  IsLeast {x | ∃ n, n > 2 ∧ V n = x} 2 := by
  constructor
  · -- Show 2 is in the set
    use 8
    constructor
    · norm_num
    · -- Show that V 8 = 2
      rw [hV 8]
      norm_num
  · -- Show 2 is minimal in the set
    intro x hx
    rcases hx with ⟨n, hn, h_eq⟩
    have h1 : n > 2 := by
      linarith
    have h2 : V n = (n^3 - 10 * n^2 + 17 * n - 4 : ℝ) / (n^2 - 10 * n + 18 : ℝ) := hV n
    rw [h2] at h_eq
    have h3 : (n^3 - 10 * n^2 + 17 * n - 4 : ℝ) / (n^2 - 10 * n + 18 : ℝ) ≥ 2 := by
      have h4 : (n : ℝ) > (2 : ℝ) := by
        exact_mod_cast (show n > 2 by linarith)
      by_cases h51 : (n : ℝ) ≥ (8 : ℝ)
      · -- Case where n ≥ 8
        have h6 : (n^2 - 10 * n + 18 : ℝ) > (0 : ℝ) := by
          nlinarith [sq_nonneg ((n : ℝ) - 5), sq_nonneg ((n : ℝ) - 7), h51]
        have h7 : (n^3 - 10 * n^2 + 17 * n - 4 : ℝ) ≥ 2 * (n^2 - 10 * n + 18 : ℝ) := by
          have hn1 : n ≥ 8 := by
            by_contra h8
            push_neg at h8
            have : n ≤ 7 := by omega
            have h7 : (n : ℝ) ≤ (7 : ℝ) := by exact_mod_cast (show n ≤ 7 by omega)
            nlinarith
          have hn8 : (n : ℝ) ≥ (8 : ℝ) := by exact_mod_cast (show n ≥ 8 by omega)
          nlinarith [sq_nonneg ((n : ℝ) - 8), sq_nonneg ((n : ℝ) - 9), sq_nonneg ((n : ℝ) - 10), sq_nonneg ((n : ℝ) - 4)]
        apply (le_div_iff₀ h6).mpr
        linarith
      · -- Case where n < 8
        have h66 : (n : ℝ) < (8 : ℝ) := by
          by_contra h8
          push_neg at h8
          have h511 : (n : ℝ) ≥ (8 : ℝ) := by linarith
          linarith
        have hn1 : n ≤ 7 := by
          by_contra h8
          push_neg at h8
          have : n ≥ 8 := by omega
          have h7 : (n : ℝ) ≥ (8 : ℝ) := by exact_mod_cast (show n ≥ 8 by omega)
          nlinarith
        have h5 : n ≤ 7 := hn1
        have h5' : n ≥ 3 := by
          omega
        have h63 : (n^2 - 10 * n + 18 : ℝ) < (0 : ℝ) := by
          have hn11 : n ≥ 3 := by omega
          have hn111 : n ≤ 7 := by omega
          have h7 : n ≤ 7 := by omega
          have h8 : n ≥ 3 := by omega
          interval_cases n <;> norm_num
        have h83 : (n^3 - 10 * n^2 + 17 * n - 4 : ℝ) ≤ 2 * (n^2 - 10 * n + 18 : ℝ) := by
          have hn11 : n ≥ 3 := by omega
          have hn111 : n ≤ 7 := by omega
          have h7 : n ≤ 7 := by omega
          have h8 : n ≥ 3 := by omega
          interval_cases n <;> norm_num
        apply (le_div_iff_of_neg' (by linarith)).mpr
        linarith
    linarith [h_eq, h3]