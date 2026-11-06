import Mathlib

theorem algebra_235305 (a : ℤ) :
    a ≠ 0 ∧ (97 * a ^ 2 + 84 * a - 55) % a = 0 ↔
    a = 1 ∨ a = 5 ∨ a = 11 ∨ a = 55 ∨ a = -1 ∨ a = -5 ∨ a = -11 ∨ a = -55 := by
  constructor
  · -- Assume $a \neq 0$ and $(97a^2 + 84a - 55) \% a = 0$
    intro h
    rcases h with ⟨ha1, ha2⟩
    have h1 : a ∣ 97 * a ^ 2 + 84 * a - 55 := by
      exact Int.dvd_of_emod_eq_zero ha2
    have h2 : a ∣ 55 := by
      have h3 : a ∣ 97 * a ^ 2 + 84 * a - 55 := h1
      have h4 : a ∣ 97 * a ^ 2 + 84 * a := by
        use 97 * a + 84
        ring
      have h5 : a ∣ (97 * a ^ 2 + 84 * a - (97 * a ^ 2 + 84 * a - 55)) := by
        apply Dvd.dvd.sub
        · exact h4
        · exact h3
      have h6 : 97 * a ^ 2 + 84 * a - (97 * a ^ 2 + 84 * a - 55) = 55 := by
        ring
      rw [h6] at h5
      exact h5
    have h3 : a ∣ 55 := h2
    have h4 : a ≤ 55 := by
      apply Int.le_of_dvd (by norm_num) h2
    have h5 : a ≥ -55 := by
      have h6 : (-a : ℤ) ∣ 55 := by 
        exact Int.neg_dvd.2 h2
      have h7 : (-a : ℤ) ≤ 55 := by 
        apply Int.le_of_dvd (by norm_num) h6
      omega
    interval_cases a <;> norm_num at h3 ⊢
  · -- Show that each of the possible values of $a$ satisfies $a \neq 0$ and the divisibility condition
    rintro (h | h | h | h | h | h | h | h) <;> 
      rw [h] <;> 
      constructor <;> 
        norm_num