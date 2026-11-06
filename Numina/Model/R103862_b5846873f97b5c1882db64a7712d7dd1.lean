import Mathlib

theorem algebra_15371 {n : ℕ} (hn : n = 24) :
    IsLeast {x | 0 < x ∧ ∀ p, p.Prime ∧ p ∣ n → p ∣ x} 6 := by
  rw [hn]
  constructor
  · -- Show 6 is in the set {x | 0 < x ∧ ∀ p, p.Prime ∧ p ∣ 24 → p ∣ x}
    constructor
    · norm_num
    · intro p hp
      rcases hp with ⟨h_prime, h_div⟩
      have h1 : p ≤ 24 := by exact Nat.le_of_dvd (by norm_num) h_div
      interval_cases p <;> norm_num at h_prime <;> norm_num at *
      <;> tauto 
  · -- Show there is no smaller element in the set
    intro x hx
    rcases hx with ⟨hx_pos, hx_div⟩
    have h2 : 2 ∣ x := hx_div 2 (⟨by norm_num, by norm_num⟩)
    have h3 : 3 ∣ x := hx_div 3 (⟨by norm_num, by norm_num⟩)
    have h6 : 6 ∣ x := by
      have h1 : 2 ∣ x := h2
      have h2 : 3 ∣ x := h3
      have h3 : Nat.Coprime (2 : ℕ) (3 : ℕ) := by norm_num
      have h4 : 2 * 3 ∣ x := by 
        exact Nat.lcm_dvd h1 h2
      have h5 : (2 : ℕ) * 3 = 6 := by norm_num
      rw [h5] at h4
      exact h4
    have hx_ge : 6 ≤ x := by
      by_contra h
      push_neg at h
      have h4 : x < 6 := h
      have h5 : x > 0 := hx_pos
      interval_cases x <;> try { norm_num at h2 h3 <;> all_goals omega }
      all_goals omega
    linarith