import Mathlib

theorem algebra_97715 {p r s : ℕ} (hp : 3 ^ p + 3 ^ 4 = 90) (hr : 2 ^ r + 44 = 76)
    (hs : 5 ^ 3 + 6 ^ s = 1421) : p * r * s = 40 := by
  have hp1 : p = 2 := by
    have h1 : 3 ^ p = 9 := by
      norm_num at hp
      omega
    have h2 : p = 2 := by
      have h3 : 3 ^ p = 9 := h1
      have h4 : p = 2 := by
        exact Nat.pow_right_injective (by norm_num) h3
      exact h4
    exact h2
  have hr1 : r = 5 := by
    have h1 : 2 ^ r = 32 := by
      omega
    have h2 : r = 5 := by
      have h3 : 2 ^ r = 32 := h1
      have h4 : r = 5 := by
        exact Nat.pow_right_injective (by norm_num) h3
      exact h4
    exact h2
  have hs1 : s = 4 := by
    have h1 : 6 ^ s = 1296 := by
      omega
    have h2 : s = 4 := by
      have h3 : 6 ^ s = 1296 := h1
      have h4 : s = 4 := by
        exact Nat.pow_right_injective (by norm_num) h3
      exact h4
    exact h2
  calc
    p * r * s = 2 * 5 * 4 := by rw [hp1, hr1, hs1]
    _ = 40 := by norm_num