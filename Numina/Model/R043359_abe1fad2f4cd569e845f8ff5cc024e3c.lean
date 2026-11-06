import Mathlib

theorem number_theory_106313 {S a b x y : ℤ} (hS : S = x + y) (hS1 : S ≠ 0)
    (h : a * x + b * y ≡ 0 [ZMOD S]) :
    a * y + b * x ≡ 0 [ZMOD S] := by 
  rw [Int.modEq_zero_iff_dvd] at h ⊢
  have h1 : S ∣ a * x + b * y := h
  have h2 : S ∣ a * y + b * x := by
    have h3 : S ∣ a * x + b * y + (a * y + b * x) := by
      have h4 : a * x + b * y + (a * y + b * x) = (a + b) * S := by
        rw [hS]
        ring
      have h5 : S ∣ (a + b) * S := by
        use a + b
        all_goals ring_nf <;> omega
      rw [h4]
      exact h5
    have h4 : (a * x + b * y + (a * y + b * x)) - (a * x + b * y) = a * y + b * x := by 
      omega
    have h5 : S ∣ (a * x + b * y + (a * y + b * x)) - (a * x + b * y) := by
      apply Int.dvd_sub
      · exact h3
      · exact h1
    rw [h4] at h5
    exact h5
  exact h2