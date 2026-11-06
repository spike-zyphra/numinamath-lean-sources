import Mathlib

theorem number_theory_120642 (a : ℕ → ℤ) (ha : ∀ n, 0 < a n)
    (h1 : a 0 < a 1) (hn : ∀(n:ℕ), 1<n → a n = 3 * a (n-1) - 2 * a (n-2)) :
    2 ^ 99 < a 100 := by

  have h2 : ∀ (n : ℕ), a n = (a 1 - a 0) * (2 ^ n) + (2 * a 0 - a 1) := by
    intro n 
    induction' n using Nat.strongRecOn with n ih 
    cases n with
    | zero =>
      simp
      <;> linarith
    | succ n =>
      cases n with
      | zero =>
        simp
        <;> linarith
      | succ n =>
        have h2 := ih (n + 1) (by linarith)
        have h3 := ih (n) (by linarith)
        have h4 : a (n + 2) = 3 * a (n + 1) - 2 * a n := by 
          specialize hn (n + 2) (by linarith)
          simpa using hn 
        rw [h4]
        rw [h2, h3]
        simp [pow_add, mul_add, mul_sub] at *
        ring_nf

  have h3 : a 100 = (a 1 - a 0) * (2 ^ 100) + (2 * a 0 - a 1) := by 
    apply h2 100

  have ha0 : 0 < a 0 := ha 0
  have ha1 : 0 < a 1 := ha 1

  have h4 : a 1 - a 0 > 0 := by linarith

  nlinarith [h3, ha0, ha1, ha 2, ha 3, ha 4, ha 5, ha 6, ha 7, ha 8, ha 9, 
          h1, h4, ha 10, ha 11, ha 12, ha 13, ha 14, ha 15, ha 16, ha 17, ha 18, ha 19, ha 20
          ]