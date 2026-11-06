import Mathlib

theorem number_theory_232698 (n : ℕ) (h₀ : n ∈ Finset.Icc 1000 9999) (h₁ : n / (n % 1000) = 3) (h₂ : n % (n % 1000) = 8) :
    n = 1496 ∨ n = 2996 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  have h5 : n % 1000 ≤ 999 := by
    omega
  have h6 : n % 1000 > 0 := by
    by_contra h
    have h7 : n % 1000 = 0 := by
      omega
    have h7 : n / (n % 1000) = 0 := by
      rw [h7]
      all_goals norm_num
    omega
  have h7 : n = 3 * (n % 1000) + 8 := by
    have h8 : n % (n % 1000) = 8 := h₂
    have h9 : n / (n % 1000) = 3 := h₁
    have h10 : n = (n % 1000) * (n / (n % 1000)) + (n % (n % 1000)) := by
      rw [Nat.div_add_mod n (n % 1000)]
    rw [h8, h9] at h10
    linarith
  interval_cases h : n % 1000 <;> omega