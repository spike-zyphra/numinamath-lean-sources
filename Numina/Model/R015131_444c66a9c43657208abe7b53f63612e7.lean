import Mathlib

open Finset

theorem number_theory_147339 {f : ℕ → ℕ} (hf : ∀ n, 0 < n → 0 < f n)
    (h : ∀ m, 1 ≤ m → ∀ n, 0 < n → f^[m] n ≠ n)
    (h' : ∃ m, 0 < m ∧ ∀ n, 0 < n → f^[m] n = n) :
    IsGreatest {k | 0 < k ∧ k < 1 ∧ ∃ f : ℕ → ℕ, (∀ n, 0 < n → 0 < f n) ∧
      (∀ m, 1 ≤ m → ∀ n, 0 < n → f^[m] n ≠ n) ∧
      (∃ m, 0 < m ∧ ∀ n, 0 < n → f^[m] n = n)} (1 - 1 / 10) := by 
  rcases h' with ⟨m, hm_pos, h_eq⟩
  have h1 := h m (by omega) 1 (by norm_num)
  have h2 := h_eq 1 (by norm_num)
  contradiction