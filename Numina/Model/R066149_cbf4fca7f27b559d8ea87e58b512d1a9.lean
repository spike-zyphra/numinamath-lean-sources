import Mathlib

theorem algebra_10269 (f : ℝ → ℝ) (hf : f = fun t => -t^2 + 12 * t + 50) :
    IsGreatest {t | f t = 77} 9 := by
  constructor
  · -- Show that 9 is in the set
    show f 9 = 77
    rw [hf]
    norm_num
  · -- Show that for all t in the set, t ≤ 9
    intro t ht
    have hht : f t = 77 := ht
    rw [hf] at hht
    simp at hht
    nlinarith [sq_nonneg (t - 9), sq_nonneg (t - 3)]