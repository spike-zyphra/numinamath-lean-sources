import Mathlib

theorem number_theory_4703 {a b : ℤ} (_ : a ≠ 0) (hb : b ≠ 0) : a ∣ b ∧ b ∣ a → a = b ∨ a = -b := by
  intro h
  rcases h with ⟨h₁, h₂⟩
  obtain ⟨k, hk⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  have h_eq : a = a * (k * m) := by
    calc
      a = b * m := by linarith [hm]
      _ = (a * k) * m := by rw [show b = a * k by linarith [hk]]
      _ = a * (k * m) := by ring
  have h_eq2 : k * m = 1 := by
    apply (mul_left_inj' (show a ≠ 0 by assumption)).mp
    linarith [h_eq]
  have h3 : k * m = 1 := h_eq2
  have hk1 : k = 1 ∨ k = -1 := by 
    apply Int.eq_one_or_neg_one_of_mul_eq_one
    exact h3
  rcases hk1 with (hk1 | hk1)
  · -- Case k = 1 
    have hm1 : m = 1 := by
      rw [hk1] at h3 
      have : (1 : ℤ) * m = 1 := by linarith 
      linarith 
    left 
    have hb_eq : b = a := by 
      rw [hk1] at hk 
      linarith 
    linarith [hb_eq, hm, hm1]
  · -- Case k = -1 
    have hm1 : m = -1 := by 
      rw [hk1] at h3 
      have : (-1 : ℤ) * m = 1 := by linarith 
      linarith 
    right 
    have hb_eq : b = -a := by 
      rw [hk1] at hk 
      linarith 
    linarith [hb_eq, hm, hm1]