import Mathlib

theorem number_theory_160935 (k : ℕ) (hk : k > 0) :
    ∃ a b c : ℤ, a^2 + b^2 = c^k := by
  use 1
  use 0
  use 1
  have h1 : (1 : ℤ) ^ 2 + (0 : ℤ) ^ 2 = (1 : ℤ) ^ k := by
    have h2 : (1 : ℤ) ^ k = 1 := by
      have h1 : ∀ (k : ℕ), (1 : ℤ) ^ k = 1 := by
        intro k
        induction k with
        | zero => 
          simp
        | succ k ih =>
          simp [pow_succ, ih]
      exact h1 k
    have h3 : (1 : ℤ) ^ 2 + (0 : ℤ) ^ 2 = 1 := by
      norm_num
    rw [h3, h2]
  exact h1