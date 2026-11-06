import Mathlib

theorem algebra_231158 {a b c M : ℤ} (h₀ : a^2 + b^2 + c^2 = M^2) (h₁ : ∃ n, a = n ∧ b = n + 1)
    (h₂ : c = a * b) :
    Odd M := by
  rcases h₁ with ⟨n, ha, hb⟩
  have hc : c = n * (n + 1) := by 
    rw [h₂, ha, hb]
  rw [hc] at h₀
  rw [ha] at h₀
  rw [hb] at h₀
  have eq : M^2 = (n^2 + n + 1)^2 := by
    nlinarith
  have h3 : M = (n^2 + n + 1) ∨ M = - (n^2 + n + 1) := by
    have eq2 : M^2 = (n^2 + n + 1)^2 := eq
    have eq3 : M^2 - (n^2 + n + 1)^2 = 0 := by
      linarith
    have eq4 : (M - (n^2 + n + 1)) * (M + (n^2 + n + 1)) = 0 := by
      ring_nf at eq3 ⊢
      linarith
    cases (mul_eq_zero.mp eq4) with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith
  rcases h3 with (h4 | h4)
  · -- Case where $M = n^2 + n + 1$
    have h7 : M % 2 = 1 := by
      have h5 : (n ^ 2 + n + 1) % 2 = 1 := by
        have h6 : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rcases h6 with (h6 | h6)
        · 
          simp [h6, pow_two, Int.add_emod, Int.mul_emod, Int.ofNat]
        · 
          simp [h6, pow_two, Int.add_emod, Int.mul_emod, Int.ofNat]
      have eq2 : M = n ^ 2 + n + 1 := by linarith [h4]
      omega
    exact ⟨M / 2, by 
      omega 
    ⟩
  · -- Case where $M = - (n^2 + n + 1)$
    have h7 : M % 2 = 1 := by
      have h5 : (n ^ 2 + n + 1) % 2 = 1 := by
        have h6 : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rcases h6 with (h6 | h6)
        · 
          simp [h6, pow_two, Int.add_emod, Int.mul_emod, Int.ofNat]
        · 
          simp [h6, pow_two, Int.add_emod, Int.mul_emod, Int.ofNat]
      have eq2 : M = - (n ^ 2 + n + 1) := by linarith [h4]
      omega
    exact ⟨M / 2, by 
      omega 
    ⟩