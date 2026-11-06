import Mathlib

/- Let $p$ be an even positive integer. Suppose that $n$ is a positive integer for which the equation $x^p + y^p = n$ admits an integer solution $(x_0, y_0)$ such that $x_0 \neq 0$, $y_0 \neq 0$, and $x_0^2 \neq y_0^2$. Show that the equation $x^p + y^p = n$ has at least 8 distinct integer solutions. -/
theorem number_theory_636132 (p : ℕ) (hp : Even p) (hp₀ : 0 < p) (n : ℕ) (hn₀ : 0 < n) (h : ∃ x₀ y₀ : ℤ, x₀ ^ p + y₀ ^ p = n ∧ x₀ ≠ 0 ∧ y₀ ≠ 0 ∧ x₀ ^ 2 ≠ y₀ ^ 2) :
    (8 : ℕ∞) ≤ {(x, y) : ℤ × ℤ | x ^ p + y ^ p = n}.encard := by
  rcases h with ⟨x₀, y₀, h, h₀, h₁, h₂⟩
  -- We first show that x₀, y₀, -x₀, -y₀ are distinct integers.
  replace h₀ : x₀ ≠ -x₀ := by
    contrapose! h₀
    linarith only [h₀]
  replace h₁ : y₀ ≠ -y₀ := by
    contrapose! h₁
    linarith only [h₁]
  replace ⟨h₂, h₃⟩ : x₀ ≠ y₀ ∧ x₀ ≠ -y₀ := by
    constructor
    all_goals
      contrapose! h₂
      simp [h₂]
  have h₄ : -x₀ ≠ y₀ := by
    contrapose! h₃
    linarith only [h₃]
  -- We show that the list given by [(x₀, y₀), (x₀, -y₀), (-x₀, y₀), (-x₀, -y₀), (y₀, x₀), (y₀, -x₀), (-y₀, x₀), (-y₀, -x₀)] has no duplicates.
  have H₁ : ({(x₀, y₀), (x₀, -y₀), (-x₀, y₀), (-x₀, -y₀), (y₀, x₀), (y₀, -x₀), (-y₀, x₀), (-y₀, -x₀)} : Multiset _).Nodup := by
    -- Simplify using our lemmas.
    simp [-not_and, h₀, h₁, h₂, h₃, h₀.symm, h₁.symm, h₂.symm, h₃.symm, h₄]
  -- We show that any member of the list is a solution to the equation.
  have H₂ : (⟨_, H₁⟩ : Finset _).toSet ⊆ {(x, y) : ℤ × ℤ | x ^ p + y ^ p = n} := by
    rintro ⟨x, y⟩ heq
    simp at heq ⊢
    -- Break down all disjunctions and conjunctions.
    cases_type* Or And
    all_goals
      -- Substitute x and y.
      subst x y
      -- Simplify using the lemma that negative powers of even numbers are positive. Use `try` to skip the cases that do not need it.
      try simp [Even.neg_pow hp]
      -- It is true by assumption.
      linear_combination h
  -- We show that the list has 8 elements.
  have H₃ : (⟨_, H₁⟩ : Finset _).toSet.encard = 8 := by
    rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_def]
    simp
  -- We conclude the set of solutions is at least as large as the list, and thus at least 8.
  have H₄ := Set.encard_mono H₂
  rwa [← H₃]