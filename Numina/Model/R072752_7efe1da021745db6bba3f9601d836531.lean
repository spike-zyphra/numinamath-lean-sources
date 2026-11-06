import Mathlib

theorem algebra_13341 {p : ℝ → ℝ} (hp : ∃ a b c d, p = fun x => a*x^3 + b*x^2 + c*x + d)
    (h2 : p 2 = 1) (h7 : p 7 = 19) (h15 : p 15 = 11) (h20 : p 20 = 29) :
    ∑ i ∈ Finset.range 21, p (i + 1) = 315 := by
  rcases hp with ⟨a, b, c, d, hp⟩
  simp [hp] at h2 h7 h15 h20 ⊢
  norm_num [Finset.sum_range_succ] at *
  linarith