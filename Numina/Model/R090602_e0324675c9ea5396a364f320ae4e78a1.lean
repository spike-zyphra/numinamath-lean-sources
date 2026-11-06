import Mathlib

open Real

theorem algebra_222684 {f g : ℝ → ℝ} (hf : f = fun x => (2 * x + 3) / (x - 1))
    (hg : ∀ x, ∃ y, g x = y ∧ f y = x + 1) :
    g 3 = 7 / 2 := by 
  have h1 := hg 3
  rcases h1 with ⟨y, hgy, hfy⟩
  have h_eq1 : f y = 4 := by
    linarith
  rw [hf] at h_eq1 
  simp at h_eq1 
  have h1 : y - 1 ≠ 0 := by 
    by_contra h
    have h2 : y = 1 := by linarith 
    rw [h2] at h_eq1 
    norm_num at h_eq1 
  field_simp [h1] at h_eq1 
  have h3 : y = 7 / 2 := by 
    linarith 
  linarith [hgy, h3]