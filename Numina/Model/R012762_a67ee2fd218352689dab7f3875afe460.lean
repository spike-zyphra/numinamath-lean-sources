import Mathlib

open Real

theorem algebra_158668 {f : ℝ → ℝ} (hf : ∃ r2 r3, ∀ x, f x = x ^ 2 - r2 * x + r3)
    (g : ℕ → ℝ) (hg0 : g 0 = 0) (hgn : ∀ n, g (n + 1) = f (g n))
    (h1 : ∀ i ∈ Finset.Icc 0 2011, g (2 * i) * g (2 * i + 2) > 0)
    (h2 : ∃ j > 0, ∀ i > j, g (i + 1) > g i)
    (h3 : ¬∃ B, ∀ n, g n ≤ B) :
    IsGreatest {A | ∀ r2 r3, (∀ x, f x = x ^ 2 - r2 * x + r3) →
      (∀ i ∈ Finset.Icc 0 2011, g (2 * i) * g (2 * i + 2) > 0) →
      (∃ j > 0, ∀ i > j, g (i + 1) > g i) →
      (∀ n, g n ≤ B)} 2 := by
  have h1' := h1 0 (by
    simp
  )
  simp [show g 0 = (0 : ℝ) by linarith [hg0]] at h1'
  all_goals linarith