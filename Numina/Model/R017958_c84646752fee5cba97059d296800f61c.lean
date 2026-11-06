import Mathlib

theorem algebra_202049 (a : ℕ → ℤ) (h₀ : ∀ n, a (n + 1) = a n + 1) (h₁ : ∑ i in Finset.range 100, a i = 2012) :
    ∑ i in Finset.range 50, a (2 * i + 2) = 1031 := by 
  have h2 : ∀ n : ℕ, a n = a 0 + (n : ℤ) := by 
    intro n
    induction n with
    | zero => 
      simp 
    | succ n ih =>
      have h3 : a (n + 1) = a n + 1 := h₀ n
      rw [h3, ih]
      simp [add_assoc, Nat.cast_add, Nat.cast_one]

  have h3 : ∀ i : ℕ, i ∈ Finset.range 100 → a i = a 0 + ↑i := by 
    intro i hi
    have h4 : a i = a 0 + ↑i := h2 i 
    simpa using h4 
  have h4 : ∑ i in Finset.range 100, a i = 100 * a 0 + 4950 := by
    have eq1 : ∑ i in Finset.range 100, a i = ∑ i in Finset.range 100, (a 0 + ↑i) := by
      apply Finset.sum_congr
      · rfl
      · intro i hi 
        have h49 : i ∈ Finset.range 100 := by
          simp at hi ⊢
          all_goals tauto
        have h100 : a i = a 0 + (↑i : ℤ) := h3 i h49
        simpa using h100 
    rw [eq1]
    have h9 : ∑ i in Finset.range 100, (a 0 + (i : ℤ)) = 100 * a 0 + 4950 := by
      have eq3 : ∑ i in Finset.range 100, (a 0 + (i : ℤ)) = 100 * a 0 + 4950 := by
        rw [Finset.sum_add_distrib]
        have h7 : ∑ i in Finset.range 100, (a 0 : ℤ) = (100 * a 0 : ℤ) := by
          simp [Finset.sum_const, Finset.card_range]
        have h10 : ∑ i in Finset.range 100, (i : ℤ) = 4950 := by 
          have h11 : ∑ i in Finset.range 100, (i : ℤ) = 4950 := by 
            norm_num [Finset.sum_range_succ]
          exact h11
        rw [h7]
        rw [h10]
        all_goals ring
      exact eq3 
    exact h9 
  -- Now the hypothesis is represented as 100 * a0 + 4950 = 2012.
  have eq2 : 100 * a 0 + 4950 = 2012 := by 
    linarith [h₁, h4]
  have eq3 : a 0 = -2938 / 100 := by 
    omega 
  exfalso
  omega