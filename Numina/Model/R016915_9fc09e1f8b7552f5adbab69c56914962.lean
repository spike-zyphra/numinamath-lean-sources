import Mathlib

theorem number_theory_311269 (a b : ℤ) (_ : 0 < a) (h₀ : 0 < b)
    (h₁ : 24 * a ^ 2 = b ^ 2 - 1) :
    (5 ∣ a) ∧ ¬(5 ∣ b) ∨ ¬(5 ∣ a) ∧ (5 ∣ b) := by

  have h2 : (5 ∣ a) ∨ (5 ∣ b) := by
    by_contra h
    push_neg at h
    have h3 : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by
      omega
    have h4 : b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by
      omega
    have ha2 : a ^ 2 % 5 = 1 ∨ a ^ 2 % 5 = 4 := by
      rcases h3 with (h | h | h | h) <;> 
        norm_num [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h] 
    have hb2 : b ^ 2 % 5 = 1 ∨ b ^ 2 % 5 = 4 := by
      rcases h4 with (h | h | h | h) <;> 
        norm_num [pow_two, Int.add_emod, Int.mul_emod, Int.sub_emod, h] 
    have h5 : (24 * a ^ 2) % 5 = (b ^ 2 - 1) % 5 := by
      omega
    have h6 : (24 * a ^ 2) % 5 = 4 * (a ^ 2 % 5) % 5 := by
      omega
    have h7 : (b ^ 2 - 1) % 5 = (b ^ 2 % 5 - 1) % 5 := by
      omega
    rw [h6, h7] at h5
    rcases ha2 with (ha2 | ha2) <;> 
      rcases hb2 with (hb2 | hb2) <;> 
        omega
  have h3 : ¬ (5 ∣ a ∧ 5 ∣ b) := by 
    intro h
    rcases h with ⟨ha, hb⟩
    obtain ⟨k, hk⟩ := ha
    obtain ⟨m, hm⟩ := hb
    rw [show a = 5 * k by linarith [hk]] at h₁
    rw [show b = 5 * m by linarith [hm]] at h₁
    ring_nf at h₁
    omega
  rcases h2 with h2 | h2
  · -- Assume 5 divides a
    have ha5 : 5 ∣ a := h2
    have hb5 : ¬(5 ∣ b) := by 
      intro hb
      exact h3 ⟨ha5, hb⟩
    left
    exact ⟨ha5, hb5⟩
  · -- Assume 5 divides b
    have ha5 : ¬(5 ∣ a) := by 
      intro ha
      exact h3 ⟨ha, h2⟩
    right
    exact ⟨ha5, h2⟩