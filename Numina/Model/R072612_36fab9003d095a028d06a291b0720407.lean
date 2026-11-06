import Mathlib

theorem algebra_10187 {f : ℕ → ℕ} (hf : ∀ x, Even x → f x = x / 2)
    (hf' : ∀ x, Odd x → f x = 3 * x + 1) : f (f (f (f 1))) = 4 := by
  have h1 : f 1 = 4 := by 
    specialize hf' 1 (by decide)
    norm_num at hf'
    exact hf'
  have h2 : f 4 = 2 := by 
    specialize hf 4 (by decide)
    norm_num at hf
    exact hf
  have h3 : f 2 = 1 := by 
    specialize hf 2 (by decide)
    norm_num at hf
    exact hf
  calc 
    f (f (f (f 1))) = f (f (f 4)) := by rw [h1]
    _ = f (f 2) := by rw [h2]
    _ = f 1 := by rw [h3]
    _ = 4 := by exact h1