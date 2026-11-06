import Mathlib

theorem algebra_168533 {f g : ℝ → ℝ} (h_odd : Function.Odd g) (hf0 : f 0 = 1)
    (hf : ∀ x y, f (x - y) = f x * f y + g x * g y) :
    (∀ x, (f x)^2 + (g x)^2 = 1) ∧ Function.Even f ∧
    ((∃ a ≠ 0, f a = 1) → ∃ c, Function.Periodic f c) := by
  have h1 : ∀ x, (f x) ^ 2 + (g x) ^ 2 = 1 := by
    intro x
    have h_eq : f (x - x) = f x * f x + g x * g x := hf x x
    have h0 : f (x - x) = f 0 := by simp
    rw [h0] at h_eq
    rw [hf0] at h_eq
    linarith
  have h2 : Function.Even f := by
    have h3 : ∀ x, f (-x) = f x := by
      intro x
      have h4 : g 0 = 0 := by
        have h5 : f (0 - (0 : ℝ)) = f (0) * f (0) + g (0) * g (0) := hf 0 0
        have h6 : f (0 - (0 : ℝ)) = f 0 := by simp
        rw [h6] at h5
        rw [hf0] at h5
        nlinarith [sq_nonneg (g 0)]
      have h7 : f (0 - x) = f 0 * f x + g 0 * g x := hf 0 x
      simp [show g 0 = 0 by linarith [h4], hf0] at h7 ⊢
      linarith [h7]
    exact h3
  have h3 : (∃ a ≠ 0, f a = 1) → ∃ c, Function.Periodic f c := by
    intro h
    rcases h with ⟨a, ha1, ha2⟩
    use 0
    simp [Function.Periodic]
  exact ⟨h1, h2, h3⟩