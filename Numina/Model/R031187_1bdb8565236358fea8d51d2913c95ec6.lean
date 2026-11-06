import Mathlib

theorem number_theory_131165 (n : ℕ) :
    7 ∣ 3^(12 * n^2 + 1) + 2^(6 * n + 2) := by
  have h1 : ∀ n : ℕ, 3 ^ (12 * n^2 + 1) % 7 = 3 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ k ih =>
      have eq1 : 3 ^ (12 * (k + 1) ^ 2 + 1) = 3 ^ (12 * k ^ 2 + 1) * 3 ^ (24 * k + 12 * 1) := by
        ring_nf
      rw [eq1]
      have h3 : 3 ^ (24 * k + 12 * 1) % 7 = 1 := by
        have h1 : ∀ m : ℕ, 3 ^ (6 * m) % 7 = 1 := by
          intro m
          induction m with
          | zero =>
            norm_num
          | succ m ih =>
            have h2 : (3 ^ (6 * m) * 3 ^ 6) % 7 = 1 := by
              rw [Nat.mul_mod]
              rw [ih]
              all_goals norm_num
            have eq3 : 3 ^ (6 * (m + 1)) = (3 ^ (6 * m) * 3 ^ 6) := by
              ring_nf
            rw [eq3] at *
            omega
        have h2 : 24 * k + 12 * 1 = 6 * (4 * k + 2) := by 
          ring_nf
        rw [h2]
        apply h1 (4 * k + 2)
      simp [Nat.add_mod, Nat.mul_mod, ih, h3] 
  have h2 : ∀ n : ℕ, (2 ^ (6 * n + 2) ) % 7 = 4 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ k ih =>
      have eq1 : (2 ^ (6 * (k + 1) + 2) ) = (2 ^ (6 * k + 2) ) * (2 ^ 6) := by
        ring_nf
      rw [eq1]
      have h4 : (2 ^ (6 * k + 2) * 2 ^ 6) % 7 = 4 := by
        simp [Nat.mul_mod, ih]
        <;> all_goals norm_num
      omega
  have h3 : 3 ^ (12 * n ^ 2 + 1) % 7 = 3 := h1 n
  have h4 : (2 ^ (6 * n + 2) ) % 7 = 4 := h2 n
  omega