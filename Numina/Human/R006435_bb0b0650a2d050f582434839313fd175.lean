import Mathlib

open Finset Nat



theorem number_theory_637031 {b Xb : ℕ} (hb : b ≥ 3) (N₁ N₂ N₃ N₄ : ℕ) (S : ℤ)
  (hN₁ : N₁ = ofDigits b [1, 2, 1]) (hN₂ : N₂ = ofDigits b [2, 2, 1, 2])
  (hN₃ : N₃ = ofDigits b [0, 0, 2, 1]) (hN₄ : N₄ = ofDigits b [1, 1, 1, 2])
  (hs : S = N₁ + N₂ - N₃ - N₄)  :
  S = -((if b = 3 then (ofDigits (b : ℕ) [1, 2, 2] : ℕ) else (ofDigits b [(b - 2), (b - 4), 0, 1]): ℕ) : ℤ) := by 
  have hn1 : ofDigits b [1, 2, 1] = 1 + 2 * b + b ^ 2 := by
    rw [Nat.ofDigits_cons, Nat.ofDigits_cons]
    simp
    ring
  have hn2 : ofDigits b [2, 2, 1, 2] = 2 + 2 * b + b ^ 2 + 2 * b ^ 3 := by
    rw [Nat.ofDigits_cons, Nat.ofDigits_cons, Nat.ofDigits_cons]
    simp
    ring
  have hn3 : ofDigits b [0, 0, 2, 1] = 2 * b ^ 2 + b ^ 3 := by
    rw [Nat.ofDigits_cons, Nat.ofDigits_cons, Nat.ofDigits_cons]
    simp
    ring 
  have hn4 : ofDigits b [1, 1, 1, 2] = 1 + b + b ^ 2 + 2 * b ^ 3 := by
    rw [Nat.ofDigits_cons, Nat.ofDigits_cons, Nat.ofDigits_cons]
    simp
    ring
  have Seq : S = - b ^ 3 - b ^ 2 + 3 * b + 2 := by 
    rw [hs, hN₁, hN₂, hN₃, hN₄, hn1, hn2, hn3, hn4]
    norm_num
    ring
  rw [Seq]
  -- Xb = if b = 3 then 2 * 3^2 + 2 * 3^1 + 1 * 3^0 else 1 * b^3 + 0 * b^2 + (b - 4) * b^1 + (b - 2) * b^0
  by_cases beq3 : b = 3 
  · -- the case b = 3
    rw [if_pos beq3, beq3]
    norm_num
    rw [Nat.ofDigits_cons, Nat.ofDigits_cons]
    simp
  · -- the case b ≥ 4
    have bge4 : b ≥ 4 := by omega
    rw [if_neg beq3]
    rw [Nat.ofDigits_cons, Nat.ofDigits_cons, Nat.ofDigits_cons]
    simp
    rw [Nat.cast_sub, Nat.cast_sub]
    norm_num
    ring
    linarith
    linarith