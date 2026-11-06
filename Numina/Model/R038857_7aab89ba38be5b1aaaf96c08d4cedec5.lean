import Mathlib

theorem algebra_243027 {a : ℕ → ℕ} (ha0 : a 0 = 0) (han : ∀ n, a (n + 1) = n + a n) :
    a 2006 = 2011015 := by
  have h1 : ∀ n, a (n + 1) = n + a n := by
    intro n
    specialize han n
    simpa using han
  -- proving a_n = n * (n - 1)/2 for all n using induction.
  have a1 : ∀ (n : ℕ), a n = (n * (n - 1)) / 2 := by
    intro n
    induction n with
    | zero =>
      simp [ha0]
    | succ n ih =>
      have h2 : a (n + 1) = n + a n := by 
        specialize h1 n
        simpa using h1
      rw [h2]
      rw [ih]
      cases n with
      | zero =>
        all_goals simp
      | succ n =>
        simp [Nat.mul_add, Nat.add_mul] at *
        <;> ring_nf at *
        <;> omega
  have h1006 : a 2006 = (2006 * (2006 - 1)) / 2 := a1 2006
  norm_num [h1006]