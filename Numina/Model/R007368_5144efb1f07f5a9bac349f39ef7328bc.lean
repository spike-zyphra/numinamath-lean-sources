import Mathlib

theorem algebra_10318 {f : ℝ → ℝ} (hf : ∀ x, x ≥ 0 → f x = -x ^ 2)
    (hf' : ∀ x, x < 0 → f x = x + 8) :
    f (f (f (f (f 1)))) = -33 := by 
  have h1 : f 1 = -1 := by 
    specialize hf 1 (by norm_num)
    norm_num at hf ⊢
    linarith

  have h2 : f (f 1) = 7 := by
    rw [h1]
    specialize hf' (-1) (by norm_num)
    norm_num at hf' ⊢
    linarith

  have h3 : f (f (f 1)) = -49 := by
    rw [h2]
    specialize hf 7 (by norm_num)
    norm_num at hf ⊢
    linarith

  have h4 : f (f (f (f 1))) = -41 := by
    rw [h3]
    specialize hf' (-49) (by norm_num)
    norm_num at hf' ⊢
    linarith

  rw [h4]
  specialize hf' (-41) (by norm_num)
  norm_num at hf' ⊢
  linarith