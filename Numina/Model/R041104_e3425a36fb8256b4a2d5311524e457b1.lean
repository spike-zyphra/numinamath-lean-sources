import Mathlib

open Finset Real

theorem algebra_158481 {f : ℝ → ℝ} (hf : ∃ r2 r3, ∀ x, f x = x ^ 2 - r2 * x + r3)
    (g : ℕ → ℝ) (hg0 : g 0 = 0) (hgn : ∀ n, g (n + 1) = f (g n))
    (h1 : ∀ i ∈ Icc 0 2011, g (2 * i) * g (2 * i + 2) ≠ 0)
    (h2 : ∃ j > 0, ∀ i > j, g (i + 1) > g i)
    (h3 : ∃ B, ∀ n, g n > B) :
    IsGreatest {A | ∀ r2 r3, (∀ x, f x = x ^ 2 - r2 * x + r3) →
      (∀ i ∈ Icc 0 2011, g (2 * i) * g (2 * i + 2) ≠ 0) →
      (∃ j > 0, ∀ i > j, g (i + 1) > g i) →
      (∃ B, ∀ n, g n > B)} 2 := by 
  have h4 : (0 : ℕ) ∈ Icc (0 : ℕ) 2011 := by
    simp [Nat.zero_le]
    all_goals omega
  have h5 := h1 0 (h4)
  rw [show (2 * (0 : ℕ) : ℕ) = 0 by omega] at h5
  rw [hg0] at h5
  norm_num at h5