import Mathlib

theorem algebra_254256 (total_surface : ℝ) (h₀ : total_surface ≠ 0)
    (water : ℝ) (land : ℝ) (h₁ : water = total_surface * 0.7) (h₂ : land = total_surface * 0.3)
    (deserts : ℝ) (pasts : ℝ) (h₃ : deserts = land * (2 / 5)) (h₄ : pasts = land * (1 / 3))
    (cogenerated : ℝ) (hcogenerated : cogenerated = total_surface - water - deserts - pasts) :
    cogenerated / total_surface * 100 = 8 := by
  have h₃' : deserts = total_surface * 0.12 := by
    rw [h₃, h₂]
    ring
  have h₄' : pasts = total_surface * 0.1 := by
    rw [h₄, h₂]
    ring
  have hc : cogenerated = total_surface * 0.08 := by
    rw [hcogenerated, h₁, h₃', h₄']
    ring
  rw [hc]
  field_simp [h₀]
  <;> ring_nf <;> norm_num
  <;> linarith