import Mathlib

open Real Filter Function
open scoped Topology

theorem calculus_32796 (F : ℕ → ℝ)
  (hF : ∀ n, F n = F (n - 1) + F (n - 2))
  (hF1 : F 1 = 1) (hF2 : F 2 = 1)
  (A : ℕ → ℝ)
  (hA : ∀ k, A (k + 1) = A k + 4 * F (2 * k + 1) / (F (2 * k + 1)^2 + 1))
  (hA1 : A 0 = 0) :
  Tendsto (λ n => A n) atTop (𝓝 (2 * π)) := by
  have h1 := hF 0
  have h2 := hF 1
  norm_num at h1 h2 hF1 hF2
  all_goals linarith