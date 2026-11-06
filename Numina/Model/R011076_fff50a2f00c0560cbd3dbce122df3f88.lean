import Mathlib

theorem algebra_10194 {f g : ℝ → ℝ} (hinv : f ∘ g = id ∧ g ∘ f = id) (hf : f 3 = 1 ∧ ∀ x, f (2 * x) = 2 * f x) :
  g 64 = 192 := by
  have hf3 : f 3 = 1 := hf.1
  have hfx : ∀ x, f (2 * x) = 2 * f x := hf.2
  have f6 : f 6 = 2 := by
    specialize hfx 3
    norm_num [hf3] at hfx ⊢
    linarith
  have f12 : f 12 = 4 := by
    specialize hfx 6
    norm_num [f6] at hfx ⊢
    linarith
  have f24 : f 24 = 8 := by
    specialize hfx 12
    norm_num [f12] at hfx ⊢
    linarith
  have f48 : f 48 = 16 := by
    specialize hfx 24
    norm_num [f24] at hfx ⊢
    linarith
  have f96 : f 96 = 32 := by
    specialize hfx 48
    norm_num [f48] at hfx ⊢
    linarith
  have f192 : f 192 = 64 := by
    specialize hfx 96
    norm_num [f96] at hfx ⊢
    linarith
  have h2 : g (f 192) = 192 := by
    simpa using congr_fun hinv.2 192
  rw [f192] at h2
  norm_num at h2 ⊢
  exact_mod_cast h2