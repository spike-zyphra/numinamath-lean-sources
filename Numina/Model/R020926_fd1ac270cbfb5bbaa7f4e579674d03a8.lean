import Mathlib

theorem algebra_10406 {f g : ℝ → ℝ} (hf : ∃ a b, f = fun x => x ^ 2 + a * x + b)
    (hg : ∃ c d, g = fun x => x ^ 2 + c * x + d) (h₁ : g 6 = 35) (h₂ : f (-1) / g (-1) = 21 / 20)
    (h₃ : f 1 / g 1 = 21 / 20) : f 6 = 35 := by

  rcases hf with ⟨a, b, hf⟩
  rcases hg with ⟨c, d, hg⟩
  have eq1 : (6 : ℝ) ^ 2 + c * (6 : ℝ) + d = 35 := by
    simp [hg] at h₁
    linarith
  have eq2 : f (-1) / g (-1) = 21 / 20 := h₂
  have eq3 : f 1 / g 1 = 21 / 20 := h₃
  have h4 : g (-1) ≠ 0 := by
    by_contra h
    have eq3 : f (-1) / g (-1) = 0 := by
      field_simp [h]
    linarith
  have h5 : g 1 ≠ 0 := by 
    by_contra h
    have eq3 : f 1 / g 1 = 0 := by 
      field_simp [h]
    linarith
  have eq4 : 20 * (f (-1)) = 21 * (g (-1)) := by
    have h1 : f (-1) / g (-1) = 21 / 20 := h₂
    field_simp [h4] at h1 ⊢
    linarith
  have eq5 : 20 * (f 1) = 21 * (g 1) := by
    have h1 : f 1 / g 1 = 21 / 20 := h₃
    field_simp [h5] at h1 ⊢
    linarith

  simp [hf, hg] at eq4 eq5
  norm_num at eq1 eq4 eq5

  have eq6 : f 6 = (6 : ℝ) ^ 2 + a * (6 : ℝ) + b := by
    simp [hf]
  norm_num at eq6
  linarith