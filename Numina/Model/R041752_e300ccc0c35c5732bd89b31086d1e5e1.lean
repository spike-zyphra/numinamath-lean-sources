import Mathlib



theorem algebra_8986 {f : ℝ → ℝ} (h : ∀ x, f (x + 5) = f x)
    (hf : ∀ x ∈ Set.Ico 0 5, f x = x ^ 2 - x) :
    f 2008 = 6 := by
  have np : ∀ (n : ℕ), ∀ x : ℝ, f (x + (↑n * 5)) = f x := by
    intro n 
    induction' n using Nat.strong_induction_on with n ih 
    cases n with 
    | zero =>
      intro x
      norm_num 
    | succ n =>
      intro x 
      have eq1 : x + (↑(n + 1 : ℕ) * 5 : ℝ) = (x + (↑n * 5 : ℝ) ) + 5 := by 
        simp at *
        <;> ring_nf 
      rw [eq1]
      have eq2 : f ((x + (↑n * 5 : ℝ) ) + 5 ) = f (x + (↑n * 5 : ℝ) ) := by 
        specialize h (x + (↑n * 5 : ℝ) )
        simpa using h 
      rw [eq2]
      have eq3 : f (x + (↑n * (5 : ℝ)) ) = f x := by 
        apply ih 
        all_goals linarith 
      simpa using eq3
  have h1 : (2008 : ℝ) = (3 : ℝ) + ((↑(401 : ℕ) : ℝ) * (5 : ℝ) ) := by 
    norm_num 
  rw [h1] 
  have h2 := np 401 3 
  rw [h2] 
  have h5 : (3 : ℝ) ∈ Set.Ico (0 : ℝ ) (5 : ℝ ) := by 
    norm_num [Set.mem_Ico]
  have h4 : f (3 : ℝ ) = (3 : ℝ ) ^ 2 - (3 : ℝ ) := hf 3 h5 
  rw [h4] 
  <;> norm_num