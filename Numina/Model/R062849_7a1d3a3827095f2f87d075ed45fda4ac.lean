import Mathlib

theorem number_theory_252109 (x : ℕ) (y : ℕ) (h₀ : x ∈ Finset.Icc 1000 9999) (h₁ : y^3 = 21 * x) :
    x = 3528 := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨hx1, hx2⟩
  have h2 : y ≤ 59 := by
    by_contra h
    push_neg at h
    have h3 : y ^ 3 > 21 * 9999 := by
      have h4 : y ≥ 60 := by linarith 
      have h5 : y^3 ≥ 60^3 := by 
        have h6 : y ≥ 60 := by linarith 
        have h7 : y ^ 3 ≥ 60 ^ 3 := by 
          apply Nat.pow_le_pow_of_le_left 
          linarith 
        linarith 
      linarith 
    linarith 
  interval_cases y <;> omega