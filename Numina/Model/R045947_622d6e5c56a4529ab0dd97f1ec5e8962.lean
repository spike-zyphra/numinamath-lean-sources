import Mathlib

theorem number_theory_16305 {a : ℕ → ℕ} (ha : ∀ n, a n = (10 ^ n - 1) / 9) :
  IsGreatest {k | ∃ n, k = Nat.gcd (a n) (a (n + 1))} 1 := by
  constructor
  · -- Show 1 is in the set
    use 0
    simp [ha]
  · -- Show no greater element is in the set
    intro k hk
    rcases hk with ⟨n, hn⟩
    rw [hn]
    have h1 : Nat.gcd (a n) (a (n + 1)) = 1 := by
      rw [ha (n + 1), ha n]
      have h2 : ∀ n : ℕ, (10 ^ (n + 1) - 1) / 9 = 10 * ((10 ^ n - 1) / 9) + 1 := by
        intro n
        induction n with
        | zero =>
          all_goals
            omega
        | succ n ih =>
          simp [Nat.pow_add, Nat.pow_one, Nat.mul_add] at ih ⊢
          all_goals
            omega
      have h2n : (10 ^ (n + 1) - 1) / 9 = 10 * ((10 ^ n - 1) / 9) + 1 := h2 n
      rw [h2n]
      simp [Nat.gcd_add_mul_self]
    omega