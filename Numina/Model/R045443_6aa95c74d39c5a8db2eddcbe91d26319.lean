import Mathlib

  theorem algebra_176317 :
  {n : ℕ | n > 9 ∧ n < 100 ∧ 100 * n + n - n ^ 2 = (n / 2) * (((4 : ℝ) / 100) * n^2) + n} = {50} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume n is in the set, prove n = 50
    rintro ⟨hn1, hn2, heq⟩
    have h1 : (n : ℝ) > (9 : ℝ) := by
      exact_mod_cast hn1
    have h2 : (n : ℝ) < (100 : ℝ) := by
      exact_mod_cast hn2
    have h3 : (100 * (n : ℝ) + (n : ℝ) - (n : ℝ) ^ 2) = (n / 2) * (((4 : ℝ) / 100) * (n : ℝ)^2) + (n : ℝ) := by
      exact_mod_cast heq
    have eq1 : (n : ℝ) ^ 3 + 50 * (n : ℝ) ^ 2 - 5000 * (n : ℝ) = 0 := by
      nlinarith [h3]
    have eq2 : (n : ℝ) * ((n : ℝ) ^ 2 + 50 * (n : ℝ) - 5000) = 0 := by
      linarith [eq1]
    cases' (mul_eq_zero.mp eq2) with h4 h5
    · -- Case where n = 0
      nlinarith
    · -- Case where quadratic equation holds
      have h7 : (n : ℝ) = (50 : ℝ) := by
        nlinarith [sq_nonneg ((n : ℝ) + 50), sq_nonneg ((n : ℝ) - 50), sq_nonneg ((n : ℝ) ^ 2 + 50 * (n : ℝ) - 5000)]
      have h8 : n = 50 := by
        exact_mod_cast h7
      exact h8
  · -- Assume n = 50, prove n is in the set
    intro h
    rw [h]
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num