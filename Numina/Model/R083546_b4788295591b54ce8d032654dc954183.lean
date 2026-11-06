import Mathlib

theorem algebra_245186 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2) :
    ¬ ∃ k, ∀ x, f x = k * x := by
  rintro ⟨k, hk⟩
  have h1 := hk 1
  have h2 := hk 2
  simp [hf] at h1 h2
  have hk1 : k = 1 := by linarith
  have hk2 : k = 2 := by linarith
  linarith