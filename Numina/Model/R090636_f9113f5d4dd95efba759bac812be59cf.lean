import Mathlib

theorem algebra_3647 (f : ℝ → ℝ) (hf : ∃ a b c d : ℝ, f = fun x => a*x^3 + b*x^2 + c*x + d)
    (h₁ : f (-1) = -8) (h₂ : f (-2) = -24) (h₃ : f 2 = 4) (h₄ : f 3 = 16) :
    f = fun x => x^3 - 2*x^2 + 3*x - 2 := by
  rcases hf with ⟨a,b,c,d,hf⟩
  have eq₁ : a * (-1) ^ 3 + b * (-1) ^ 2 + c * (-1) + d = -8 := by
    simpa [hf] using h₁
  have eq₂ : a * (-2) ^ 3 + b * (-2) ^ 2 + c * (-2) + d = -24 := by
    simpa [hf] using h₂
  have eq₃ : a * 2 ^ 3 + b * 2 ^ 2 + c * 2 + d = 4 := by
    simpa [hf] using h₃
  have eq₄ : a * 3 ^ 3 + b * 3 ^ 2 + c * 3 + d = 16 := by
    simpa [hf] using h₄
  have h_a : a = 1 := by
    ring_nf at eq₁ eq₂ eq₃ eq₄
    linarith [eq₁, eq₂, eq₃, eq₄]
  have h_b : b = -2 := by
    ring_nf at eq₁ eq₂ eq₃ eq₄
    linarith [eq₁, eq₂, eq₃, eq₄]
  have h_c : c = 3 := by
    ring_nf at eq₁ eq₂ eq₃ eq₄
    linarith [eq₁, eq₂, eq₃, eq₄]
  have h_d : d = -2 := by
    ring_nf at eq₁ eq₂ eq₃ eq₄
    linarith [eq₁, eq₂, eq₃, eq₄]
  ext x
  simp [hf, h_a, h_b, h_c, h_d]
  all_goals ring_nf