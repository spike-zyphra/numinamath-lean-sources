import Mathlib
open Nat

theorem number_theory_600015 : (2011^(2010^2000)) % 100 = 1 := by
  have h1 : ∀ (k : ℕ), (2011 ^ (40 * k)) % 100 = 1 := by
    intro k
    induction k with
    | zero =>
      norm_num
    | succ k ih =>
      simp [Nat.pow_add, Nat.pow_mul] at ih ⊢
      all_goals
        omega
  -- Show that the exponent 2010^2000 is divisible by 40
  have h2 : (2010 ^ 2000) % 40 = 0 := by
    norm_num
  have h3 : ∃ k, (2010 ^ 2000) = 40 * k := by
    have h4 : 40 ∣ 2010 ^ 2000 := by
      omega
    rcases h4 with ⟨k, hk⟩
    refine ⟨k, by omega⟩
  rcases h3 with ⟨k, hk⟩
  rw [hk]
  apply h1 k