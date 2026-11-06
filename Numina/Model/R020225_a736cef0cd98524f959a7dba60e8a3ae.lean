import Mathlib

theorem algebra_18785 (x : ℕ) : (17^6 - 17^5) / 16 = 17^x ↔ x = 5 := by
  constructor
  · -- Forward direction: if (17^6 - 17^5) / 16 = 17^x, then x = 5
    intro h
    have h1 : (17^6 - 17^5) / 16 = 17 ^ 5 := by
      norm_num
      <;> omega
    rw [h1] at h
    have h2 : x = 5 := by
      have h3 : 17 ^ 5 = 17 ^ x := by
        exact_mod_cast h
      have h4 : 5 = x := by
        exact Nat.pow_right_injective (by norm_num) h3
      omega
    exact h2
  · -- Backward direction: if x = 5, then (17^6 - 17^5) / 16 = 17^x
    intro h
    rw [h]
    norm_num
    <;> omega