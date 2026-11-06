import Mathlib

theorem algebra_276647 (n : ℕ) (hn : n ≥ 1) (a : ℕ → ℝ)
    (h₀ : ∀ k ∈ Finset.range n, a k = a 0 + 4 * k) (h₁ : a 0 ^ 2 + ∑ i ∈ Finset.range (n - 1), a (i + 1) ≤ 100) :
    n ≤ 8 := by
  by_contra h
  push_neg at h
  have h2 : n ≥ 9 := by omega
  have eq1 : ∀ (k : ℕ), k < n → a k = a 0 + (4 * (k : ℝ)) := by
    intro k hk
    specialize h₀ k (by
      simp at *
      all_goals
        omega
    )
    simpa using h₀
  have eq2 : ∀ (i : ℕ), i < n - 1 → a (i + 1) = a 0 + (4 * ((i + 1 : ℝ))) := by
    intro i hi
    have h3 : i + 1 < n := by
      omega
    specialize eq1 (i + 1) h3
    simpa using eq1
  have eq3 : ∑ i ∈ Finset.range (n - 1), a (i + 1) = ∑ i ∈ Finset.range (n - 1), (a 0 + (4 * ((i + 1 : ℝ)))) := by
    apply Finset.sum_congr
    · rfl
    · intro i hi
      have h4 : i < n - 1 := by
        simp at hi ⊢
        all_goals
          omega
      specialize eq2 i h4
      simpa using eq2
  have eq4 : ∑ i ∈ Finset.range (n - 1), (a 0 + (4 * ((i + 1 : ℝ)))) = (n - 1 : ℝ) * a 0 + 2 * ((n - 1 : ℝ) * (n : ℝ)) := by
    have h5 : ∀ (n : ℕ), n ≥ 1 → ∑ i ∈ Finset.range (n - 1), (a 0 + (4 * ((i + 1 : ℝ)))) = (n - 1 : ℝ) * a 0 + 2 * ((n - 1 : ℝ) * (n : ℝ)) := by
      intro n hn
      induction n with
      | zero => 
        linarith -- this case is excluded by hn
      | succ n ih =>
        cases n with
        | zero =>
          simp -- For n = 1, LHS sum has range 0, sum is 0. RHS is 0.
        | succ n =>
          norm_num at ih ⊢
          <;> simp [Finset.sum_range_succ] at ih ⊢
          <;> nlinarith [sq_nonneg (a 0), sq_nonneg (a 0 + (4 * (↑n : ℝ))), sq_nonneg ((4 * (↑n : ℝ)))]
    specialize h5 n hn
    simpa using h5
  have h3 : a 0 ^ 2 + ((n - 1 : ℝ) * a 0 + 2 * ((n - 1 : ℝ) * (n : ℝ)) ) ≤ (100 : ℝ) := by
    have h4 : ∑ i ∈ Finset.range (n - 1), a (i + 1) = ∑ i ∈ Finset.range (n - 1), (a 0 + (4 * ((i + 1 : ℝ)))) := eq3
    have eq5 : ∑ i ∈ Finset.range (n - 1), (a 0 + (4 * ((i + 1 : ℝ)))) = (n - 1 : ℝ) * a 0 + 2 * ((n - 1 : ℝ) * (n : ℝ)) := eq4
    have h6 : ∑ i ∈ Finset.range (n - 1), a (i + 1) = (n - 1 : ℝ) * a 0 + 2 * ((n - 1 : ℝ) * (n : ℝ)) := by linarith [h4, eq5]
    nlinarith [h₁, h6]
  have h4 : n ≥ 9 := h2
  have h5 : (n : ℝ) ≥ (9 : ℝ) := by exact_mod_cast h4
  nlinarith [sq_nonneg ((n : ℝ) - 9), sq_nonneg (a 0 + 4 * (n : ℝ)), sq_nonneg (a 0 - 0), sq_nonneg (a 0 - (-18)), sq_nonneg ((n : ℝ) * (a 0 - (-18))), sq_nonneg ((a 0 + 36) - (0)), sq_nonneg ((a 0 + 36) - (0)), sq_nonneg ((a 0 + 36) - (0)), sq_nonneg ((a 0 + 36) - (0)), sq_nonneg ((a 0 + 36) - (0)), sq_nonneg ((n * (a 0 : ℝ)) - (-324)), sq_nonneg ((n : ℝ) - 9), sq_nonneg ((n : ℝ) - 9)]