import Mathlib
open Int

theorem number_theory_93581 : IsGreatest {x | ∀ n : ℤ, x ∣ n ^ 3 - n} 6 := by
  constructor
  · -- Show 6 is in the set
    intro n
    have h1 : n ^ 3 % 6 = n % 6 := by
      have h2 : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
        omega
      rcases h2 with (h | h | h | h | h | h) <;> 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
    have h2 : (n ^ 3 - n) % 6 = 0 := by
      have h3 : n ^ 3 % 6 = n % 6 := h1
      omega
    exact Int.dvd_of_emod_eq_zero h2
  · -- Show that 6 is greatest in the set
    intro x hx
    have h2 := hx 2
    have h3 : x ∣ 6 := by
      norm_num at h2 ⊢
      exact h2
    have h4 : x ≤ 6 := by
      apply Int.le_of_dvd (by norm_num) h3
    linarith