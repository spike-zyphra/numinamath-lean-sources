import Mathlib

theorem algebra_274061 (x : ℕ) (h : 512 ^ x = 64 ^ 240) : x = 160 := by
  have h1 : (512 : ℕ) ^ x = 2 ^ (9 * x) := by
    have h10 : ∀ (n : ℕ), (512 : ℕ) ^ n = 2 ^ (9 * n) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        calc
          (512 : ℕ) ^ (n + 1) = (512 : ℕ) ^ n * 512 := by ring
          _ = (2 ^ (9 * n)) * 512 := by rw [ih]
          _ = 2 ^ (9 * n) * 2 ^ 9 := by norm_num
          _ = 2 ^ (9 * (n + 1)) := by ring_nf
    specialize h10 x
    exact h10 
  have h2 : (64 : ℕ) ^ 240 = 2 ^ 1440 := by
    norm_num
  rw [h1, h2] at h 
  have h3 : 9 * x = 1440 := by
    exact Nat.pow_right_injective (by norm_num) h 
  omega