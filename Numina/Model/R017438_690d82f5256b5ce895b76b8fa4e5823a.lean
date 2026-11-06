import Mathlib

theorem number_theory_232403 (n : ℕ) (h₀ : n ∈ Finset.Icc 1000 9999) (h₁ : ∀ i, (n / 10 ^ i) % 10 = (n / 10 ^ (i - 1)) + 1) :
    n - (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) = 3087 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₂, h₃⟩
  exfalso 
  have h9 := h₁ 0
  have h99 := h₁ 1
  norm_num at h9 h99
  all_goals omega