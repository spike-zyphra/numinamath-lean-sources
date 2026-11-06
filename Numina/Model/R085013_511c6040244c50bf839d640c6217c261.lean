import Mathlib

theorem algebra_183739 (s : ℕ → ℝ)
    (h₀ : s 9 = 387)
    (h₁ : s 10 = s 9 + 269)
    (h₂ : s 11 = s 9 + s 10 - 55)
    (h₃ : s 12 = (s 9 + s 10 + s 11) / 3) :
    ∑ i ∈ Finset.Icc 9 12, s i < 2950 := by
  norm_num [Finset.sum_Icc_succ_top, h₀, h₁, h₂, h₃] at *
  all_goals norm_num