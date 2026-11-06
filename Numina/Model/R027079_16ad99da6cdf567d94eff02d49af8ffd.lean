import Mathlib

theorem number_theory_151177 (n : ℕ) (h₀ : n ∈ Finset.Icc 1000 9999) (h₁ : (n / 1000) % 100 + (n / 100) % 100 = (n / 1000) % 100) (h₂ : (n / 1000) % 100 + (n / 100) % 100 < 2 * (n / 10) % 10) (h₃ : {p | p.Prime ∧ p = (n / 1000) % 100 ∨ p.Prime ∧ p = (n / 100) % 100 ∨ p.Prime ∧ p = (n / 10) % 10 ∨ p.Prime ∧ p = n % 10}.encard = 1) :
    n = 1970 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₄, h₅⟩
  have h1 : (n / 1000) % 100 + (n / 100) % 100 = (n / 1000) % 100 := h₁
  have h1' : (n / 1000) % 100 = n / 1000 := by
    omega
  have h2' : (n / 100) % 100 = n / 100 := by
    omega
  -- Rewrite h₁ using h1', h2'
  have h1_eq : (n / 1000) + (n / 100) = n / 1000 := by
    omega
  -- From h1_eq: (n / 1000) + (n / 100) = n / 1000
  -- This implies n / 100 = 0 by subtracting (n / 1000) from both sides.
  have h5 : n / 100 = 0 := by
    omega
  -- This is a contradiction with n >= 1000, so n/100 >= 10.
  omega