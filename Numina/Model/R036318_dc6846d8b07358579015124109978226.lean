import Mathlib

theorem number_theory_143114 (f : ℕ → ℕ)
    (h₀ : ∀ n, 0 < n → f n = f 1 ∨ ∃ p, Nat.Prime p ∧ f n = 1)
    (h₁ : ∀ a b, 0 < a → 0 < b → f (a * b) = a * f b + f a * b) :
    (∀ n, 0 < n → f n = n) ↔
    (∀ n, 0 < n → f n = 1 ∨ ∃ p, Nat.Prime p ∧ f n = 1) := by 
  have h2 := h₁ 1 1 (by norm_num) (by norm_num)
  simp at h2 
  have h3 : f 1 = 0 := by 
    omega 
  constructor 
  · -- Assume that $f n = n$ for all $n$. Prove the second part
    intro h 
    have h4 := h 1 (by norm_num) 
    omega
  · -- Assume the second part, prove the first.
    intro h 
    -- Show contradiction
    have h4 := h 1 (by norm_num) 
    have h5 := h₀ 1 (by norm_num)
    simp [h3] at h4 h5 
    all_goals omega