import Mathlib

theorem number_theory_195420 (k n a b : ℤ) (h₀ : k ≠ 0) (h₁ : n ≠ 0)
    (h₂ : k * a ≡ k * b [ZMOD k * n]) : a ≡ b [ZMOD n] := by
  have h₃ : (k * a - k * b) % (k * n) = 0 := by
    have h₄ : (k * a : ℤ) % (k * n) = (k * b : ℤ) % (k * n) := by 
      exact h₂ 
    have h₅ : (k * a - k * b) % (k * n) = 0 := by
      rw [Int.sub_emod]
      rw [h₄]
      simp
    exact h₅
  have h₆ : k * n ∣ k * (a - b) := by 
    have h₇ : (k * a - k * b) % (k * n) = 0 := h₃ 
    have h₈ : k * n ∣ k * a - k * b := by 
      exact Int.dvd_of_emod_eq_zero h₇ 
    have h₉ : k * a - k * b = k * (a - b) := by 
      ring 
    rw [h₉] at h₈
    exact h₈ 
  have h₇ : n ∣ a - b := by 
    obtain ⟨m, hm⟩ := h₆ 
    -- So $k * (a - b) = k * (m * n)$.
    have h₈ : k * (a - b) = k * (m * n) := by 
      linarith 
    -- Since k ≠ 0, we can cancel k from both sides.
    have h₉ : a - b = m * n := by 
      apply (mul_left_inj' h₀).mp 
      linarith 
    -- Therefore, n divides a - b
    exact ⟨m, by linarith⟩ 
  exact Int.ModEq.symm (Int.modEq_of_dvd h₇)