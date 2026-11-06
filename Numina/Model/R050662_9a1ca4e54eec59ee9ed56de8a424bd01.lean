import Mathlib

theorem number_theory_4123 (k : ℤ) (hk : k > 0) (h : 100 < k ∧ k < 200)
    (h1 : 102 ∣ 204^3 - k^3 - 101^3) : k = 103 := by
  rcases h with ⟨h10, h20⟩
  have h3 : k < 200 := h20
  have h4 : k > 100 := h10
  interval_cases k <;> norm_num at h1 <;> omega