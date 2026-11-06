import Mathlib

theorem number_theory_283964 (a : ℕ) (ha : a > 0) :
    ∃ x y : ℤ, x^2 - y^2 = a^3 := by 
  have h1 : a ≥ 1 := by linarith
  have h2 : (a : ℤ) % 2 = 0 ∨ (a : ℤ) % 2 = 1 := by omega 
  rcases h2 with (h2 | h2)
  · -- a is even
    have h3 : (a : ℤ) % 2 = 0 := h2
    -- From h3, a is even in ℤ, so a = 2k for some k in ℕ.
    have h4 : ∃ k : ℤ, (a : ℤ) = 2 * k := by
      refine' ⟨(a : ℤ) / 2, ?_⟩ 
      omega 
    rcases h4 with ⟨k, h5⟩
    use (2 * k ^ 2 + k), (2 * k ^ 2 - k)
    have eq1 : ( (2 * k ^ 2 + k) : ℤ ) ^ 2 - ( (2 * k ^ 2 - k) : ℤ ) ^ 2 = ( (a : ℤ) ^ 3 ) := by 
      rw [show (a : ℤ) = 2 * k by linarith [h5] ]
      ring_nf 
    exact_mod_cast eq1 
  · -- a is odd 
    have h3 : (a : ℤ) % 2 = 1 := h2 
    -- From h3, need to show a is odd 
    have h4 : ∃ k : ℤ, (a : ℤ) = 2 * k + 1 := by
      refine' ⟨(a : ℤ) / 2, ?_⟩ 
      omega
    rcases h4 with ⟨k, h5⟩ 
    use (2 * k ^ 2 + 3 * k + 1), (2 * k ^ 2 + k)
    have eq1 : ( (2 * k ^ 2 + 3 * k + 1) : ℤ ) ^ 2 - ( (2 * k ^ 2 + k) : ℤ ) ^ 2 = ( (a : ℤ) ^ 3 ) := by 
      rw [show (a : ℤ) = 2 * k + 1 by linarith [h5] ]
      ring_nf 
    exact_mod_cast eq1