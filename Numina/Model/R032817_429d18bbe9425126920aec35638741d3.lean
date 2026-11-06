import Mathlib

theorem algebra_214352 (a : ℕ → ℝ) (ha1 : a 1 = 1)
    (han : ∀ n ≥ 2, a n = 1 / (4 * a (n - 1)) + 1 / n) :
    a 100 = 101 / 200 := by 
  have h1 : ∀ (n : ℕ), a (n + 1) = ( (n + 2 : ℝ) ) / (2 * ( (n + 1 : ℝ) )) := by
    intro n 
    induction n with 
    | zero =>
      norm_num [ha1]
    | succ n ih =>
      have h2 : ((n + 1 + 1 : ℕ)) = (n + 2 : ℕ) := by omega 
      have eq1 : a ((n + 1 + 1 : ℕ)) = 1 / (4 * a ( (n + 1 + 1 : ℕ) - 1 ) ) + 1 / (↑(n + 1 + 1 : ℕ) ) := by 
        specialize han ((n + 1 + 1 : ℕ) ) (by omega)
        simpa using han
      have eq3 : ( (n + 1 + 1 : ℕ) - 1 ) = (n + 1 : ℕ) := by omega
      have h3 : a ( (n + 1 + 1 : ℕ) ) = 1 / (4 * a ( (n + 1 + 1 : ℕ) - 1 ) ) + 1 / (↑(n + 1 + 1 : ℕ) ) := eq1
      have h4 : ( (n + 1 : ℕ) + 1 ) = ( (n + 1 : ℕ) + 1 ) := by rfl 
      rw [h3]
      rw [eq3]
      rw [ih]
      field_simp at *
      ring_nf
  have h100 := h1 99 
  norm_num at h100 ⊢ 
  linarith [h100]