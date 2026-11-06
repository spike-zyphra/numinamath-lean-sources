import Mathlib

theorem number_theory_2626
    (min_not_divisor : ℕ → ℕ)
    (h_min_not_divisor : ∀ n, IsLeast {m | ¬ m ∣ n} (min_not_divisor n)) :
    min_not_divisor (min_not_divisor 19 * min_not_divisor 98) = 4 := by
  have h₁ : IsLeast {m | ¬ m ∣ 0} (min_not_divisor 0) := h_min_not_divisor 0
  have h2 : {m | ¬ m ∣ 0} = ∅ := by
    ext n
    simp [Nat.dvd_zero]
  rw [h2] at h₁
  simp [IsLeast] at h₁