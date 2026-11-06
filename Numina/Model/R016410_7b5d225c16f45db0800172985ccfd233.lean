import Mathlib

theorem number_theory_208570 (a : ℕ → ℕ)
    (h₀ : a 0 = 1)
    (h₁ : ∀ n, a (n + 1) = ∑ i in Finset.Icc 1 (n + 1), (a i)^2 + n + 1) :
    ∀ n, IsSquare (a n) → n = 0 := by
  intro n hn
  have eq1 := h₁ 0
  norm_num [Finset.sum_Icc_succ_top, h₀] at eq1
  all_goals
  try { 
    exfalso
    <;> nlinarith [sq_nonneg (a 1 - 1), sq_nonneg (a 1), sq_nonneg (a 0 - 1), h₀, sq_nonneg (a 1), sq_nonneg (a 1 - 1)]
  }
  all_goals
  try { 
    exfalso
    <;> nlinarith
  }
  all_goals
  try { 
    nlinarith [sq_nonneg (a 1 - 1), sq_nonneg (a 1), sq_nonneg (a 0 - 1), h₀, sq_nonneg (a 1), sq_nonneg (a 1 - 1)]
  }