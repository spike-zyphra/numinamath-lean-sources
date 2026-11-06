import Mathlib

theorem algebra_326816 (f : ℝ → ℝ) (hodd : ∀ x, f (-x) = -f x)
    (hf : ∀ x, f (x + 2) = f x + 2) :
    ∑ k in Finset.range 2014, f (k + 1) = 2029105 := by
  have h0 : f 0 = 0 := by
    have h0 : f (-0 : ℝ) = -f 0 := hodd 0
    simp at h0 
    linarith
  have h1 : f 1 = 1 := by
    have h1_eq : f (1 : ℝ) = f (-1 : ℝ) + 2 := by
      specialize hf (-1)
      norm_num at hf ⊢
      linarith
    have hodd1 : f (-1 : ℝ) = -f 1 := hodd 1
    rw [hodd1] at h1_eq
    linarith
  have h2 : ∀ (n : ℕ), f (n : ℝ) = (n : ℝ) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      cases n with
      | zero =>
        norm_num [h0]
      | succ n =>
        cases n with
        | zero =>
          norm_num [h1]
        | succ n =>
          have eq1 : f ((n + 2 : ℕ) : ℝ) = f ((n : ℕ) : ℝ) + 2 := by
            specialize hf ((n : ℝ))
            norm_num at hf ⊢
            <;> linarith
          have eq2 : f ((n : ℕ) : ℝ) = (n : ℝ) := by
            apply ih 
            all_goals
              simp_all [Nat.lt_succ_iff]
          rw [eq1]
          rw [eq2]
          all_goals
            norm_num
            <;> linarith
  have h4 : ∀ (k : ℕ), f ((k + 1 : ℝ)) = (k + 1 : ℝ) := by
    intro k
    specialize h2 (k + 1)
    simpa using h2
  have h5 : ∑ k in Finset.range 2014, f ((k + 1 : ℝ)) = 
      ∑ k in Finset.range 2014, (k + 1 : ℝ) := by
    apply Finset.sum_congr
    · rfl 
    · intro k hk
      have h6 : f ((k + 1 : ℝ)) = (k + 1 : ℝ) := by
        specialize h4 k
        simpa using h4
      simpa using h6
  rw [h5]
  norm_num [Finset.sum_range_succ]