import Mathlib

theorem algebra_228206 {f : ℕ → ℕ} (h : ∀ n, f (f n) + f n = 2 * n + 3) :
    f 1993 = 1994 := by

  have h1 : ∀ n, f n = n + 1 := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      have eq1 : f (f 0) + f 0 = 3 := by 
        specialize h 0
        simpa using h
      have h2 : f 0 ≤ 3 := by
        by_contra h3
        push_neg at h3
        have h3' : f 0 ≥ 4 := by omega
        have h4 : f (f 0) = 0 := by
          have h3' : f 0 ≥ 4 := by omega
          omega
        have h5 : f 0 = 3 := by
          omega
        omega
      have h30 : f 0 = 0 ∨ f 0 = 1 ∨ f 0 = 2 ∨ f 0 = 3 := by 
        omega
      rcases h30 with (h_eq | h_eq | h_eq | h_eq)
      · 
        exfalso
        have h0 : f 0 = 0 := h_eq
        rw [h0] at eq1
        omega
      · 
        omega
      · 
        have h0 : f 0 = 2 := h_eq
        have eq2 : f (f 0) + f 0 = 3 := eq1
        rw [h0] at eq2
        have h19 : f 2 = 1 := by 
          omega
        have eq3 : f (f 2) + f 2 = 7 := by
          specialize h 2
          simpa using h
        have h20 : f 1 = 6 := by
          rw [show f 2 = 1 by omega] at eq3
          omega
        have eq4 : f (f 1) + f 1 = 5 := by
          specialize h 1
          simpa using h
        exfalso
        rw [h20] at eq4
        omega
      · 
        exfalso
        have h0 : f 0 = 3 := h_eq
        have eq2 : f (f 0) + f 0 = 3 := eq1
        rw [h0] at eq2
        have h110 : f 3 = 0 := by
          omega
        have eq3 : f (f 3) + f 3 = 9 := by
          specialize h 3
          simpa using h
        rw [h110] at eq3
        omega
    | succ n =>
      have h3 : f n = n + 1 := ih n (by linarith)
      have eq1 : f (f n) + f n = 2 * n + 3 := h n
      rw [h3] at eq1
      have h4 : f (n + 1) = n + 2 := by
        omega
      simp [h4]
      all_goals omega
  have h1993 : f 1993 = 1993 + 1 := h1 1993
  omega