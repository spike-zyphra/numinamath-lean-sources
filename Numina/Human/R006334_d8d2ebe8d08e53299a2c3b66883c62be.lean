import Mathlib

open Nat

def max_four (a b c d : ℕ) : ℕ := max (max a b) (max c d)

def min_four (a b c d : ℕ) : ℕ := min (min a b) (min c d)

theorem number_theory_636000 (m N₁ N₂ N₃ N₄ : ℕ) (hm : m > 0) (hn1 : N₁ = 15 ^ (2 * m))
  (hn2 : N₂ = 3 ^ (8 * m)) (hn3 : N₃ = 4 ^ (4 * m)) (hn4 : N₄ = 25 ^ m):
  (max_four N₁ N₂ N₃ N₄) * (min_four N₁ N₂ N₃ N₄) = 405^(2*m) := by 
  have hn1' : N₁ = 225 ^ m := by 
    rw [hn1, pow_mul]
    norm_num
  have hn2' : N₂ = 6561 ^ m := by
    rw [hn2, pow_mul]
    norm_num
  have hn3' : N₃ = 256 ^ m := by
    rw [hn3, pow_mul]
    norm_num
  have h1 : max_four N₁ N₂ N₃ N₄ = N₂ := by 
    unfold max_four
    have aux1 : (N₃ ⊔ N₄) = N₃ := by 
      refine Nat.max_eq_left ?_
      rw [hn3', hn4]
      apply pow_le_pow_of_le_left
      linarith 
    have aux2 : N₁ ⊔ N₂ = N₂ := by 
      refine Nat.max_eq_right ?_
      rw [hn2', hn1']
      apply pow_le_pow_of_le_left
      linarith 
    rw [aux1, aux2]
    refine Nat.max_eq_left ?_
    rw [hn2', hn3']
    apply pow_le_pow_of_le_left
    linarith 
  have h2 : min_four N₁ N₂ N₃ N₄ = N₄ := by
    unfold min_four 
    have aux1 : (N₃ ⊓ N₄) = N₄ := by 
      refine Nat.min_eq_right ?_
      rw [hn3', hn4]
      apply pow_le_pow_of_le_left
      linarith 
    have aux2 : N₁ ⊓  N₂ = N₁ := by 
      refine Nat.min_eq_left ?_
      rw [hn2', hn1']
      apply pow_le_pow_of_le_left
      linarith 
    rw [aux1, aux2]
    refine Nat.min_eq_right ?_
    rw [hn1', hn4]
    apply pow_le_pow_of_le_left
    linarith 
  rw [h1, h2]
  rw [hn2', hn4, pow_mul, ←mul_pow]
  norm_num