import Mathlib


theorem number_theory_282093 (n : ℕ) (h : Even n) :
    1957 ∣ 183^n - 126^n := by
  rcases h with ⟨k, hk⟩
  have h1 : n = 2 * k := by linarith
  have h2 : (183 ^ n : ℕ) % 19 = (126 ^ n : ℕ) % 19 := by
    rw [show n = 2 * k by linarith]
    have h4 : ∀ k : ℕ, (183 ^ (2 * k) : ℕ) % 19 = (126 ^ (2 * k) : ℕ) % 19 := by
      intro k
      induction k with
      | zero => 
        norm_num
      | succ k ih =>
        simp [Nat.pow_add, Nat.pow_mul, Nat.mul_mod] at ih ⊢
        all_goals omega
    specialize h4 k
    simpa using h4

  have h3 : (183 ^ n : ℕ) % 103 = (126 ^ n : ℕ) % 103 := by
    rw [show n = 2 * k by linarith]
    have h4 : ∀ k : ℕ, (183 ^ (2 * k) : ℕ) % 103 = (126 ^ (2 * k) : ℕ) % 103 := by
      intro k
      induction k with
      | zero => 
        norm_num
      | succ k ih =>
        simp [Nat.pow_add, Nat.pow_mul, Nat.mul_mod] at ih ⊢
        all_goals norm_num at ih ⊢
        all_goals omega
    specialize h4 k
    simpa using h4

  omega