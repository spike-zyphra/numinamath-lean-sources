import Mathlib

open Finset Real

theorem inequalities_380 (a : ℕ → ℝ) (ha : ∀ i ∈ Icc 1 10, 0 < a i)
    (h : ∀ i ∈ Icc 1 9, a i ≥ a (i + 1)) (h1 : a 1 + a 2 ≤ 10)
    (h2 : ∑ i ∈ Icc 3 10, a i ≤ 10) :
    ∑ i ∈ Icc 1 10, (a i)^2 ≤ 100 := by
  have h31 : a 1 ≥ a 2 := h 1 (by norm_num)
  have h32 : a 2 ≥ a 3 := h 2 (by norm_num)
  have h33 : a 3 ≥ a 4 := h 3 (by norm_num)
  have h34 : a 4 ≥ a 5 := h 4 (by norm_num)
  have h35 : a 5 ≥ a 6 := h 5 (by norm_num)
  have h36 : a 6 ≥ a 7 := h 6 (by norm_num)
  have h37 : a 7 ≥ a 8 := h 7 (by norm_num)
  have h38 : a 8 ≥ a 9 := h 8 (by norm_num)
  have h39 : a 9 ≥ a 10 := h 9 (by norm_num)
  have h10 : a 1 > 0 := ha 1 (by norm_num)
  have h20 : a 2 > 0 := ha 2 (by norm_num)
  have h30 : a 3 > 0 := ha 3 (by norm_num)
  have h40 : a 4 > 0 := ha 4 (by norm_num)
  have h50 : a 5 > 0 := ha 5 (by norm_num)
  have h60 : a 6 > 0 := ha 6 (by norm_num)
  have h70 : a 7 > 0 := ha 7 (by norm_num)
  have h80 : a 8 > 0 := ha 8 (by norm_num)
  have h90 : a 9 > 0 := ha 9 (by norm_num)
  have h100 : a 10 > 0 := ha 10 (by norm_num)
  norm_num [sum_Icc_succ_top] at h2 ⊢
  -- On this corrected proof, we don't expand summation as explicitly complex expressions
  -- nlinarith works better here after simplification
  all_goals nlinarith
  all_goals try nlinarith
  all_goals tauto