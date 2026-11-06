import Mathlib

theorem algebra_287818 (f : ℕ → ℝ → ℝ) (hf : ∀ x, f 0 x = x ^ 2)
    (hroots : ∀ i ∈ Finset.range 2020, ∃ x y, x ≠ y ∧ f i x = 0 ∧ f i y = 0 ∧ x - y = i + 1) :
    ∃ x y, x ≠ y ∧ f 2019 x = 0 ∧ f 2019 y = 0 ∧ x - y = 2020 := by
  have h1 := hroots 2019 (by 
    native_decide
  )
  rcases h1 with ⟨x, y, hxne, hfx, hfy, hdiff⟩
  refine ⟨x, y, hxne, hfx, hfy, by 
    norm_num at hdiff ⊢
    linarith
  ⟩