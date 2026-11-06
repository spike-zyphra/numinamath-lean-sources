import Mathlib

theorem algebra_123146 {f : ℕ → ℕ} (h : ∀ n, f n + f (f n) + f (f (f n)) = 3 * n) :
    ∀ n, f n = n := by
  intro n
  induction' n using Nat.strongRecOn with n ih
  by_cases h10 : n < 1
  · -- n < 1, so n = 0
    have hn0 : n = 0 := by
      omega
    rw [hn0]
    have h0 := h 0
    have h1 := h (f 0)
    have h2 := h (f (f 0))
    have h3 := h (f (f (f 0)))
    omega
  · -- n >= 1
    -- induction step
    have eq1 := h n
    have eq2 := h (f n)
    have eq3 := h (f (f n))
    have eq4 := h (f (f (f n)))
    -- substitute the induction hypothesis
    -- if f m = m for all m < n
    -- then f (f n) = f n (because f n < n)
    -- and f (f (f n)) = f n (because f (f n) < n)
    -- so f n + f n + f n = 3n, so f n = n
    by_cases h5 : f n < n
    · -- if f n < n, then according to the induction hypothesis, we have f (f n) = f n
      have eq5 := ih (f n) h5
      simp [eq5] at eq1 eq2 eq3
      try { 
        have eq6 : f n = n := by
          omega
        assumption
      }
      all_goals omega
    · -- f n >= n
      by_cases h6 : f (f n) < n
      · -- if f (f n) < n, then f (f (f n)) = f (f n)
        have eq6 := ih (f (f n)) h6
        simp [eq6] at eq1 eq2 eq3
        all_goals
          try { 
            have eq7 : f n = n := by
              omega
            assumption
          }
          all_goals omega
      · -- f (f n) >= n
        by_cases h7 : f (f (f n)) < n
        · -- if f (f (f n)) < n, then f (f (f n)) = f (f n)
          have eq7 := ih (f (f (f n)) ) h7
          simp [eq7] at eq1 eq2 eq3
          all_goals
            try { 
              have eq8 : f n = n := by
                omega
              assumption
            }
            all_goals omega
        · -- f (f (f n)) >= n
          -- but contradiction here, since n >= 1
          -- all the expressions in n >=1 would create a loop
          all_goals
            try { 
              omega
              <;> try { 
                exfalso
                <;> try { 
                  omega
                }
                <;> try { 
                  tauto
                  <;> try { 
                    exfalso
                  }
                  <;> try { 
                    omega
                  }
                }
                <;> try { 
                  exfalso
                }
                <;> try { 
                  exfalso
                }
              }
            }
            try { 
              have eq5 : f n = n := by 
                omega 
              assumption
            }
            try { 
              -- let last-resungs automatic solving
              exfalso
              <;> try { 
                omega
              }
              <;> try { 
                exfalso
                <;> try { 
                  omega
                }
              }
            }