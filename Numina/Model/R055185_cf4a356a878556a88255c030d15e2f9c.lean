import Mathlib

def is_juicy (n : ℕ) := n % 10 = 5 ∨ n % 10 = 1

theorem number_theory_155030 {j1 j2 : ℕ} (hj1 : is_juicy j1) (hj2 : is_juicy j2) :
    is_juicy (j1 * j2) := by 
  rcases hj1 with (hj1 | hj1)
  · rcases hj2 with (hj2 | hj2)
    · -- j1 % 10 = 5, j2 % 10 = 5
      simp [is_juicy]
      have h1 : (j1 * j2) % 10 = 5 := by 
        simp [Nat.mul_mod, hj1, hj2]
      omega 
    · -- j1 % 10 = 5, j2 % 10 = 1
      simp [is_juicy]
      have h1 : (j1 * j2) % 10 = 5 := by 
        simp [Nat.mul_mod, hj1, hj2]
      omega 
  · rcases hj2 with (hj2 | hj2)
    · -- j1 % 10 = 1, j2 % 10 = 5
      simp [is_juicy]
      have h1 : (j1 * j2) % 10 = 5 := by 
        simp [Nat.mul_mod, hj1, hj2]
      omega 
    · -- j1 % 10 = 1, j2 % 10 = 1
      simp [is_juicy]
      have h1 : (j1 * j2) % 10 = 1 := by 
        simp [Nat.mul_mod, hj1, hj2]
      omega