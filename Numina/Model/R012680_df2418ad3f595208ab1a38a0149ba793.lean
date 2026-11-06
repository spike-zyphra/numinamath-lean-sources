import Mathlib

theorem algebra_326268 {f : ℝ → ℝ} (h : ∀ x, f (x + 1) = f x + 1) :
    Set.ncard {x | f x = x} = 0 ∨ Set.Infinite {x | f x = x} := by 
  by_cases h1 : ∀ x, f x ≠ x
  · -- If there is no solution, then the set is empty, so cardinality 0
    have h2 : {x | f x = x} = ∅ := by
      ext x
      simp [h1]
    rw [h2]
    simp
  · -- If there exists a solution, then the set is infinite
    push_neg at h1
    rcases h1 with ⟨x0, hx0⟩
    have h3 : Set.Infinite {x | f x = x} := by
      apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => x0 + (↑n : ℝ))
      · -- Show f is injective 
        intro n m hnm
        have h1 : x0 + (↑n : ℝ) = x0 + (↑m : ℝ) := by 
          simpa using hnm 
        have h2 : (↑n : ℝ) = (↑m : ℝ) := by 
          linarith 
        have h4 : n = m := by 
          exact_mod_cast (show (↑n : ℝ) = (↑m : ℝ) by linarith) 
        exact h4 
      · -- Show all values are in the set 
        intro n 
        have h4 : ∀ (n : ℕ), f (x0 + (↑n : ℝ)) = x0 + (↑n : ℝ) := by 
          intro n 
          induction n with 
          | zero => 
            simp [hx0] 
          | succ n ih => 
            have eq1 : x0 + (↑(n + 1 : ℕ) : ℝ) = (x0 + (↑n : ℝ)) + 1 := by 
              simp 
              <;> ring 
            rw [eq1] 
            rw [show f ((x0 + (↑n : ℝ)) + 1) = f (x0 + (↑n : ℝ)) + 1 by 
              specialize h (x0 + (↑n : ℝ)) 
              simpa using h
            ] 
            rw [ih] 
            all_goals 
              simp 
              <;> ring
        specialize h4 n 
        simpa using h4 
    right 
    exact h3