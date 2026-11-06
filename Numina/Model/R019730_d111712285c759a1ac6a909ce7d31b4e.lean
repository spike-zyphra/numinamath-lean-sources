import Mathlib

theorem algebra_8746 {f : ℝ → ℝ} (h : ∀ x, f x + f (1 - x) = 1) (h' : ∀ x, f x = 2 * f (x / 5))
    (h'' : ∀ x₁ x₂ : ℝ, 0 ≤ x₁ ∧ x₁ ≤ x₂ ∧ x₂ ≤ 1 → f x₁ ≤ f x₂) :
    f (1 / 2022) = 1 / 32 := by
  have h1 : f 0 = 0 := by
    have eq1 := h 0
    have eq2 := h' 0
    norm_num at eq1 eq2
    linarith
  have h2 : f 1 = 1 := by
    have eq1 := h 0
    rw [h1] at eq1
    norm_num at eq1 ⊢
    linarith
  have h3 : f (1 / 5 : ℝ) = 1 / 2 := by
    have eq1 := h' 1
    rw [h2] at eq1
    norm_num at eq1 ⊢
    linarith
  have h4 : f (1 / 25 : ℝ) = 1 / 4 := by
    have eq1 := h' (1 / 5 : ℝ)
    rw [h3] at eq1
    norm_num at eq1 ⊢
    linarith
  have h5 : f (1 / 125 : ℝ) = 1 / 8 := by
    have eq1 := h' (1 / 25 : ℝ)
    rw [h4] at eq1
    norm_num at eq1 ⊢
    linarith
  have h6 : f (1 / 625 : ℝ) = 1 / 16 := by
    have eq1 := h' (1 / 125 : ℝ)
    rw [h5] at eq1
    norm_num at eq1 ⊢
    linarith
  have h7 : f (1 / 3125 : ℝ) = 1 / 32 := by
    have eq1 := h' (1 / 625 : ℝ)
    rw [h6] at eq1
    norm_num at eq1 ⊢
    linarith
  have h8 : f (1 / 3125 : ℝ) ≤ f (1 / 2022 : ℝ) := by
    apply h''
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  have h9 : f (1 / 2022 : ℝ) ≤ f (1 / 625 : ℝ) := by
    apply h''
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  have h10 : 1 / 32 ≤ f (1 / 2022 : ℝ) := by
    linarith [h7, h8]
  have h11 : f (1 / 2022 : ℝ) ≤ 1 / 16 := by
    linarith [h6, h9]
  have h41 : f (4 / 5 : ℝ) = 1 / 2 := by
    have eq1 : f (1 / 5 : ℝ) + f (1 - (1 / 5 : ℝ)) = 1 := h (1 / 5 : ℝ)
    have eq2 : f (1 - (1 / 5 : ℝ)) = f (4 / 5 : ℝ) := by ring_nf
    rw [eq2] at eq1
    linarith [eq1, h3]
  have h42 : f (4 / 25 : ℝ) = 1 / 4 := by
    have h4 : f (4 / 5 : ℝ) = 2 * f ((4 / 5 : ℝ) / 5 : ℝ) := h' (4 / 5 : ℝ)
    have h5' : ((4 / 5 : ℝ) / 5 : ℝ) = (4 / 25 : ℝ) := by norm_num
    rw [h5'] at h4
    linarith [h41, h4]
  have h43 : f (4 / 125 : ℝ) = 1 / 8 := by
    have h4 : f (4 / 25 : ℝ) = 2 * f ((4 / 25 : ℝ) / 5 : ℝ) := h' (4 / 25 : ℝ)
    have h5' : ((4 / 25 : ℝ) / 5 : ℝ) = (4 / 125 : ℝ) := by norm_num
    rw [h5'] at h4
    linarith [h42, h4]
  have h44 : f (4 / 625 : ℝ) = 1 / 16 := by
    have h4 : f (4 / 125 : ℝ) = 2 * f ((4 / 125 : ℝ) / 5 : ℝ) := h' (4 / 125 : ℝ)
    have h5' : ((4 / 125 : ℝ) / 5 : ℝ) = (4 / 625 : ℝ) := by norm_num
    rw [h5'] at h4
    linarith [h43, h4]
  have h45 : f (4 / 3125 : ℝ) = 1 / 32 := by
    have h4 : f (4 / 625 : ℝ) = 2 * f ((4 / 625 : ℝ) / 5 : ℝ) := h' (4 / 625 : ℝ)
    have h5' : ((4 / 625 : ℝ) / 5 : ℝ) = (4 / 3125 : ℝ) := by norm_num
    rw [h5'] at h4
    linarith [h44, h4]
  have h17 : f (1 / 2022 : ℝ) ≤ f (4 / 3125 : ℝ) := by
    apply h''
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  have h18 : f (1 / 2022 : ℝ) ≤ 1 / 32 := by
    linarith [h45, h17]
  linarith [h10, h18]