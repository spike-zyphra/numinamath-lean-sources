import Mathlib

theorem algebra_16538 {n : ℕ} (hn : n > 0) (h : ∃ k, n = k^2) (h1 : 4 ∣ n) (h2 : 39 < n) (h3 : n < 80) :
    n = 64 := by
  rcases h with ⟨k, rfl⟩
  have h4 : k > 6 := by nlinarith
  have h5 : k < 9 := by nlinarith
  interval_cases k <;> norm_num at *
  <;> omega