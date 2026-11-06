import Mathlib

theorem algebra_108263 {a : ℕ → ℤ} (ha0 : a 0 = 1) (ha1 : a 1 = 2)
    (han : ∀ n, a (n + 2) = if Even (a n * a (n + 1)) then 5 * a (n + 1) - 3 * a n else a (n + 1) - a n) :
    ∀ n, a n ≠ 0 := by

  have ha2 : ∀ n, a n % 3 = 1 + (n % 2) := by
    intro n 
    induction' n using Nat.strongRecOn with n ih
    cases n with
    | zero =>
      rw [ha0]
      all_goals omega 
    | succ n =>
      cases n with 
      | zero =>
        rw [ha1]
        all_goals omega 
      | succ n =>
        have h1 := ih (n) (by linarith)
        have h2 := ih (n + 1) (by linarith)
        have h3 : a (n + 2) % 3 = 1 + ((n + 2) % 2) := by
          have h4 : a (n + 2) = if Even (a n * a (n + 1)) then 5 * a (n + 1) - 3 * a n else a (n + 1) - a n := han n
          rw [h4]
          by_cases h : Even (a n * a (n + 1))
          · -- case where $a_n \cdot a_{n+1}$ is even 
            simp [h] 
            have h5 : (a n : ℤ) % 3 = 1 + (n % 2) := h1
            have h6 : (a (n + 1) : ℤ) % 3 = 1 + ((n + 1) % 2) := h2
            by_cases h' : n % 2 = 0 
            · -- n is even 
              have h8 : (a n : ℤ) % 3 = 1 := by 
                rw [h5]
                omega 
              have h9 : (a (n + 1) : ℤ) % 3 = 2 := by 
                rw [h6]
                omega 
              omega 
            · -- n is odd 
              have h8 : (a n : ℤ) % 3 = 2 := by 
                rw [h5]
                omega 
              have h9 : (a (n + 1) : ℤ) % 3 = 1 := by 
                rw [h6]
                omega 
              omega 
          · -- case where $a_n \cdot a_{n+1}$ is odd 
            simp [h] 
            have h5 : (a n : ℤ) % 3 = 1 + (n % 2) := h1
            have h6 : (a (n + 1) : ℤ) % 3 = 1 + ((n + 1) % 2) := h2
            by_cases h' : n % 2 = 0 
            · -- n is even 
              have h8 : (a n : ℤ) % 3 = 1 := by 
                rw [h5]
                omega 
              have h9 : (a (n + 1) : ℤ) % 3 = 2 := by 
                rw [h6]
                omega 
              omega 
            · -- n is odd 
              have h8 : (a n : ℤ) % 3 = 2 := by 
                rw [h5]
                omega 
              have h9 : (a (n + 1) : ℤ) % 3 = 1 := by 
                rw [h6]
                omega 
              omega 
        exact h3 
  intro n 
  have h1 := ha2 n 
  have h2 : a n % 3 = 1 ∨ a n % 3 = 2 := by 
    omega 
  by_contra h 
  have h3 : a n % 3 = 0 := by 
    omega 
  omega 
  all_goals omega