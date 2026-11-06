import Mathlib
open Nat

theorem number_theory_240457 (m n : ℕ) (h : 3^m * n = Nat.factorial 7 + Nat.factorial 8 + Nat.factorial 9) :
    IsLeast {x | ∃ m n, x = n ∧ 3^m * n = Nat.factorial 7 + Nat.factorial 8 + Nat.factorial 9} 560 := by 
  constructor
  · -- First, show 560 is in the set.
    use 6, 560
    all_goals
    norm_num [Nat.factorial]
  · -- Now, show there's no smaller element in the set
    intro x hx
    rcases hx with ⟨m, n, hx_eq, heq⟩
    by_contra h'
    push_neg at h'
    have h1 : n < 560 := by 
      omega
    have h2 : 3^m * n = 408240 := by
      norm_num [Nat.factorial] at heq ⊢
      omega
    have h3 : m ≤ 6 := by
      by_contra h4
      push_neg at h4
      have h5 : m > 6 := by omega
      have h6 : 3 ^ 7 ∣ 3 ^ m := by
        have h7 : 7 ≤ m := by omega
        exact pow_dvd_pow _ (by omega)
      have h7 : 3 ^ 7 ∣ 408240 := by
        have h8 : 3 ^ 7 ∣ 3 ^ m := h6
        have h9 : 3 ^ m ∣ 408240 := by
          use n
          linarith [h2]
        exact dvd_trans h8 h9
      norm_num at h7
    -- From h2: $3^m \cdot n = 408240$, and m ≤ 6.
    have h4 : n ≥ 560 := by
      have h5 : m ≤ 6 := h3
      have h6 : 3 ^ m ≤ 729 := by
        have h7 : m ≤ 6 := h3
        have h8 : 3 ^ m ≤ 3 ^ 6 := by 
          apply Nat.pow_le_pow_of_le_right (by norm_num) h7
        have h9 : 3 ^ 6 = 729 := by norm_num
        linarith
      nlinarith
    omega