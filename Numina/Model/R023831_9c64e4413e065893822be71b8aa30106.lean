import Mathlib

theorem algebra_302087 {a : ℕ → ℝ} (h : ∀ n, a n - a (n - 1) = a (n - 1) - a (n - 2)) :
    ∃ d, ∀ n, a (n + 1) = a n + d := by
  have eq1 := h 1
  norm_num at eq1 
  have eq2 := h 2
  norm_num at eq2
  have eq3 : a 1 = a 0 := by linarith
  have eq4 : a 2 = a 0 := by linarith [eq2, eq3]
  have h1 : ∀ (n : ℕ), a n = a 0 := by 
    intro n 
    induction' n using Nat.strongRecOn with n ih 
    cases n with 
    | zero =>
      simp 
    | succ n => 
      cases n with 
      | zero =>
        -- Base case n = 1.
        -- Show a 1 = a 0.
        have h1a : a 1 = a 0 := eq3 
        simp [h1a]
      | succ n => 
        cases n with 
        | zero =>
          -- Base case n = 2.
          -- Show a 2 = a 0.
          have h2a : a 2 = a 0 := eq4 
          simp [h2a]
        | succ n => 
          -- Inductive step for n \ge 3.
          -- Show a (n + 1) = a 0 for n+1 \ge 3.
          have ih1 := ih (n + 1) (by omega)
          have ih2 := ih (n + 2) (by omega)
          have eq5 := h (n + 3)
          norm_num [show n + 3 ≥ 1 by omega] at eq5 
          simp [ih1, ih2] at eq5 ⊢ 
          all_goals linarith 
  use 0 
  intro n 
  have eq5 : a n = a 0 := h1 n 
  have eq6 : a (n + 1) = a 0 := by 
    specialize h1 (n + 1) 
    simpa using h1 
  linarith [eq5, eq6]