import Mathlib

theorem number_theory_4870 {N : ℕ} (hN : N % 2023 = 2019) : N % 289 = 285 := by
  have h1 : N % 289 = 285 := by
    have h3 : N % 2023 = 2019 := hN
    norm_num at h3 ⊢
    omega
  exact h1