import Mathlib

theorem number_theory_628031 (n : ℕ) (h : n = 48^(2022)) :
    (n % 7 = 1) := by
  rw [h]
  have h2 : ∀ k : ℕ, (48 ^ (2 * k) : ℕ) % 7 = 1 := by
    intro k 
    induction k with
    | zero =>
      norm_num
    | succ k ih =>
      have h3 : (48 ^ (2 * (k + 1)) : ℕ) % 7 = 1 := by 
        calc
          (48 ^ (2 * (k + 1)) : ℕ) % 7 = (48 ^ (2 * k) * 48 ^ 2) % 7 := by 
            ring_nf
          _ = ((48 ^ (2 * k) : ℕ) % 7 * (48 ^ 2) % 7) % 7 := by
            simp [Nat.mul_mod]
          _ = (1 * (48 ^ 2) % 7) % 7 := by
            rw [ih]
          _ = ( (48 ^ 2) % 7 ) % 7 := by
            simp
          _ = (1) % 7 := by
            norm_num
          _ = 1 := by
            norm_num
      simpa using h3
  have : (2022 : ℕ) = 2 * (1011 : ℕ) := by
    norm_num
  rw [this]
  specialize h2 1011
  simpa using h2