import Mathlib

theorem number_theory_167885 (a : ℕ) (ha : 0 < a) :
    ∃ x y : ℤ, x ^ 2 - y ^ 2 = a ^ 3 := by
  use (a ^ 2 + a) / 2, (a ^ 2 - a) / 2
  have h1 : (a : ℤ) > 0 := by exact_mod_cast ha
  have h_eq : ( (a ^ 2 + a) / 2 : ℤ ) ^ 2 - ( (a ^ 2 - a) / 2 : ℤ ) ^ 2 = (a : ℤ) ^ 3 := by
    by_cases h : (a : ℤ) % 2 = 0
    · -- if `a` is even
      have h3 : ∃ k : ℤ, (a : ℤ) = 2 * k := by 
        refine' ⟨a / 2, by omega⟩
      rcases h3 with ⟨k, hk⟩
      have eq1 : ( (a ^ 2 + a) / 2 : ℤ ) = 2 * k ^ 2 + k := by
        rw [show (a : ℤ) = 2 * k by linarith [hk]]
        ring_nf
        <;> omega
      have eq2 : ( (a ^ 2 - a) / 2 : ℤ ) = 2 * k ^ 2 - k := by
        rw [show (a : ℤ) = 2 * k by linarith [hk]]
        ring_nf
        <;> omega
      rw [eq1, eq2]
      rw [show (a : ℤ) = 2 * k by linarith [hk]]
      ring_nf
    · -- if `a` is odd
      have h4 : (a : ℤ) % 2 = 1 := by omega
      have h3 : ∃ k : ℤ, (a : ℤ) = 2 * k + 1 := by
        have h4 : (a : ℤ) % 2 = 1 := by omega
        have h5 : (a : ℤ) % 2 = 1 := h4
        have h12 : ∃ k : ℤ, (a : ℤ) = 2 * k + 1 := by 
          have h13 : (a : ℤ) % 2 = 1 := h4
          have : (a : ℤ) = (2 * (a / 2) + 1) := by
            omega
          refine' ⟨a / 2, by linarith⟩
        exact_mod_cast h12
      rcases h3 with ⟨k, hk⟩
      have eq1 : ( (a ^ 2 + a) / 2 : ℤ ) = 2 * k ^ 2 + 3 * k + 1 := by
        rw [show (a : ℤ) = 2 * k + 1 by linarith [hk]]
        ring_nf
        <;> omega
      have eq2 : ( (a ^ 2 - a) / 2 : ℤ ) = 2 * k ^ 2 + k := by
        rw [show (a : ℤ) = 2 * k + 1 by linarith [hk]]
        ring_nf
        <;> omega
      rw [eq1, eq2]
      rw [show (a : ℤ) = 2 * k + 1 by linarith [hk]]
      ring_nf
  simp [h_eq]