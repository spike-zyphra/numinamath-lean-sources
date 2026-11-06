import Mathlib

theorem algebra_108047 {a : ℕ → ℤ} (ha : a 1 = 1) (ha' : a 2 = 3)
    (ha'' : ∀ n, a (n + 2) = 3 * a (n + 1) - 2 * a n) :
    ∀ n, a n = 2 ^ n - 1 := by 
  have ha0 : a 0 = 0 := by
    have eq1 := ha'' 0 
    simp [ha, ha'] at eq1 
    linarith 
  intro n 
  have h1 : ∀ n : ℕ, a n = 2 ^ n - 1 := by
    intro n 
    induction' n using Nat.strongRecOn with n ih 
    cases n with 
    | zero =>
      simp [ha0]
    | succ n =>
      cases n with 
      | zero =>
        simp [ha]
      | succ n =>
        cases n with 
        | zero =>
          simp [ha']
        | succ n =>
          have eq1 := ha'' (n + 1)
          simp [show n + 1 + 2 = n + 3 by omega] at eq1 
          have h1 := ih (n + 2) (by omega)
          have h2 := ih (n + 1) (by omega)
          simp [eq1, h1, h2]
          ring_nf 
          <;> omega 
  exact h1 n