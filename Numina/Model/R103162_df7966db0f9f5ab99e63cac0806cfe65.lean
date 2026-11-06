import Mathlib

theorem number_theory_258957 (n : ℤ) :
    IsSquare (n^2 + 15) ↔ n = -7 ∨ n = -1 ∨ n = 1 ∨ n = 7 := by
  constructor
  · -- Forward direction: if $n^2 + 15$ is a square, then $n \in \{-7, -1, 1, 7\}$.
    rintro h
    rcases h with ⟨m, hm⟩
    -- We have $n^2 + 15 = m^2$ for some integer $m$.
    -- Rearrange to get $m^2 - n^2 = 15$, which factors as $(m - n)(m + n) = 15$.
    have h1 : m^2 = n^2 + 15 := by
      nlinarith
    -- Simplify to standard form.
    have h2 : m^2 - n^2 = 15 := by 
      linarith
    -- Factor the equation as a product.
    have h3 : (m - n) * (m + n) = 15 := by 
      nlinarith
    -- Use the fact that $m - n$ must be a divisor of 15.
    have h4 : m - n ∣ 15 := by
      use m + n
      all_goals nlinarith
    have h5 : m - n ≤ 15 := by
      apply Int.le_of_dvd (by norm_num) h4
    have h6 : m - n ≥ -15 := by
      have h7 : -(m - n) ∣ 15 := by 
        exact Int.neg_dvd.2 h4
      have h8 : -(m - n) ≤ 15 := by
        apply Int.le_of_dvd (by norm_num) h7
      linarith
    -- Use interval reasoning to solve finite cases.
    interval_cases k : m - n <;> 
      try { 
        omega
      }
    all_goals 
      try { 
        omega
      }
  · -- Backward direction: if $n \in \{-7, -1, 1, 7\}$, then $n^2 + 15$ is a square.
    rintro (rfl | rfl | rfl | rfl)
    · -- Case $n = -7$
      use -8
      norm_num
    · -- Case $n = -1$
      use -4
      norm_num
    · -- Case $n = 1$
      use 4
      norm_num
    · -- Case $n = 7$
      use 8
      norm_num