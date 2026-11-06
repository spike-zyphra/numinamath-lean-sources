import Mathlib

open Finset

theorem algebra_161305 (a : ℕ → ℝ)
    (h₀ : a 1 = 1)
    (h₁ : a 2 = 2)
    (h₂ : ∀ n, a (n + 2) = a (n + 1) / a n) :
    ∑ i ∈ range 1730, a (i + 1) = 2019 := by

  have ha3 : a 3 = 2 := by
    specialize h₂ 1
    rw [show 1 + 2 = (3 : ℕ) by omega] at h₂
    rw [h₀, h₁] at h₂
    norm_num at h₂ ⊢
    linarith

  have ha4 : a 4 = 1 := by
    specialize h₂ 2
    rw [show 2 + 2 = (4 : ℕ) by omega] at h₂
    rw [h₁, ha3] at h₂
    norm_num at h₂ ⊢
    linarith

  have ha5 : a 5 = 1 / 2 := by
    specialize h₂ 3
    rw [show 3 + 2 = (5 : ℕ) by omega] at h₂
    rw [ha3, ha4] at h₂
    norm_num at h₂ ⊢
    linarith

  have ha6 : a 6 = 1 / 2 := by
    specialize h₂ 4
    rw [show 4 + 2 = (6 : ℕ) by omega] at h₂
    rw [ha4, ha5] at h₂
    norm_num at h₂ ⊢
    linarith

  have ha7 : a 7 = 1 := by
    specialize h₂ 5
    rw [show 5 + 2 = (7 : ℕ) by omega] at h₂
    rw [ha5, ha6] at h₂
    norm_num at h₂ ⊢
    linarith

  have ha8 : a 8 = 2 := by
    specialize h₂ 6
    rw [show 6 + 2 = (8 : ℕ) by omega] at h₂
    rw [ha6, ha7] at h₂
    norm_num at h₂ ⊢
    linarith

  set_option maxRecDepth 10000 in
  norm_num [sum_range_succ, h₀, h₁, ha3, ha4, ha5, ha6, ha7, ha8, h₂]