import Mathlib

theorem number_theory_1486 (n d : ℕ) (h1 : d ∣ 19 * n + 14) (h2 : d ∣ 10 * n + 3) (h3 : d ≠ 1) :
    d = 83 := by 
  have h4 : d ∣ 10 * (19 * n + 14) - 19 * (10 * n + 3) := by 
    apply Nat.dvd_sub'
    · -- Show that d divides 10 * (19n + 14)
      apply Nat.dvd_trans h1
      norm_num 
    · -- Show that d divides 19 * (10n + 3)
      apply Nat.dvd_trans h2
      norm_num 
  have h5 : 10 * (19 * n + 14) - 19 * (10 * n + 3) = 83 := by
    omega 
  rw [h5] at h4
  have h6 : d = 1 ∨ d = 83 := by 
    have h7 : d ∣ 83 := h4 
    have h8 : d ≤ 83 := Nat.le_of_dvd (by norm_num) h7 
    interval_cases d <;> norm_num at * 
    <;> tauto 
  cases h6 with
  | inl h => 
    exfalso 
    exact h3 (by 
      omega 
    )
  | inr h => 
    exact h