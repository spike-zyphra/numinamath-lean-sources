import Mathlib

open Finset

theorem inequalities_40329 {f : ℕ → ℕ} (hf : ∀ n, 0 < n → 0 < f n)
    (h : ∀ n, (n - 1)^2020 < ∏ l ∈ Icc 1 2020, f^[l] n ∧ f^[l] n < n^2020 + n^2019) :
    ∀ n, 0 < n → f n = n := by

  have h0 := h 0
  norm_num at h0
  all_goals linarith