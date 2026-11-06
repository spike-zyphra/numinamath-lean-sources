import Mathlib

theorem algebra_11290 {a : ℕ → ℤ} (h : ∀ n, a (n + 2) = 3 * a (n + 1) - 2 * a n)
    (ha : a 1 = 1) (hb : a 2 = 3) :
    ∀ n, a n = 2 ^ n - 1 := by
  -- First, establish a₀ = 0 as h0
  have h0 : a 0 = 0 := by 
    have eq1 := h 0
    simp at eq1 
    linarith [ha, hb]
  intro n 
  induction' n using Nat.strongRecOn with n ih
  cases n with 
  | zero =>
    simp [h0]
  | succ n =>
    cases n with
    | zero =>
      simp [ha]
    | succ n =>
      cases n with
      | zero =>
        simp [hb]
      | succ n =>
        have h3 := h (n + 1)
        -- h6 establishes a(n+2)
        have h6 : a (n + 2) = 3 * a (n + 1) - 2 * a n := by 
          specialize h n
          simpa using h
        have h4 := ih (n + 1) (by linarith)
        have h5 := ih (n) (by linarith)
        have eq3 : a (n + 2) = 2 ^ (n + 2) - 1 := by
          rw [h6]
          rw [h4, h5]
          ring_nf 
          <;> omega 
        have eq1 := h (n + 1)
        have eq2 : a (n + 3) = 3 * a (n + 2) - 2 * a (n + 1) := by 
          simpa using eq1 
        have eq4 : a (n + 3) = 2 ^ (n + 3) - 1 := by
          rw [eq2]
          rw [eq3, h4]
          ring_nf 
          <;> omega 
        simpa using eq4