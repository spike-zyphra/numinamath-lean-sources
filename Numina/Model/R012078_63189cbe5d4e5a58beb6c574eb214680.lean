import Mathlib

theorem algebra_173257 {a b c n p q r s : ℝ} (h₀ : p = n * a + (n + 1) * b + (n + 1) * c)
    (h₁ : q = (n + 3) * a + (n + 2) * b + (n + 3) * c) (h₂ : r = (n + 3) * a + (n + 3) * b + (n + 2) * c)
    (h₃ : s = (p + q + r) / 3) (h₄ : p' = 2 * s - p) (h₅ : q' = 2 * s - q)
    (h₆ : r' = 2 * s - r) :
    ∀ k ∈ Finset.Icc 1 2, p ^ k + q ^ k + r ^ k = p' ^ k + q' ^ k + r' ^ k := by
  intro k hk
  rw [Finset.mem_Icc] at hk
  rcases hk with ⟨hk1, hk2⟩
  have hk_eq_1 : k = 1 ∨ k = 2 := by
    omega
  rcases hk_eq_1 with (rfl | rfl)
  -- case k=1
  · -- k=1, prove the sum is equal
    have eq1 : p + q + r = p' + q' + r' := by
      rw [h₄, h₅, h₆]
      rw [h₃]
      ring_nf
    simp [eq1]
  -- case k=2
  · -- k=2, prove the sum of squares is equal
    have eq2 : p ^ 2 + q ^ 2 + r ^ 2 = p' ^ 2 + q' ^ 2 + r' ^ 2 := by
      rw [h₄, h₅, h₆]
      rw [h₃]
      ring_nf
    simp [eq2]