import Mathlib

theorem algebra_286465 (n : ℕ) (h₀ : n > 0) (h₁ : ∃ k, k^2 = n^2 + 19 * n + 48) :
    n = 33 := by
  rcases h₁ with ⟨k, hk⟩
  have h2 : k^2 = n^2 + 19 * n + 48 := hk
  have h3 : (2 * k : ℤ)^2 = 4 * (n ^ 2 + 19 * n + 48 : ℤ) := by
    have h4 : (k : ℤ)^2 = (n ^ 2 + 19 * n + 48 : ℤ) := by exact_mod_cast h2
    nlinarith
  have h4 : (2 * n + 19 : ℤ)^2 - (2 * k : ℤ)^2 = 169 := by
    nlinarith [h3]
  have h6 : ((2 * n + 19 : ℤ) - (2 * k : ℤ)) * ((2 * n + 19 : ℤ) + (2 * k : ℤ)) = 169 := by
    nlinarith [h4]
  have h7 : ((2 * n + 19 : ℤ) - (2 * k : ℤ)) ∣ 169 := by
    use ((2 * n + 19 : ℤ) + (2 * k : ℤ))
    linarith
  have h8 : ((2 * n + 19 : ℤ) - (2 * k : ℤ)) ≤ 169 := by
    apply Int.le_of_dvd (by norm_num) h7
  have h9 : ((2 * n + 19 : ℤ) - (2 * k : ℤ)) ≥ -169 := by
    have h10 : (- ((2 * n + 19 : ℤ) - (2 * k : ℤ))) ∣ 169 := by
      exact Int.neg_dvd.2 h7
    have h11 : (- ((2 * n + 19 : ℤ) - (2 * k : ℤ))) ≤ 169 := by
      apply Int.le_of_dvd (by norm_num) h10
    linarith
  interval_cases h : ((2 * n + 19 : ℤ) - (2 * k : ℤ)) <;> omega