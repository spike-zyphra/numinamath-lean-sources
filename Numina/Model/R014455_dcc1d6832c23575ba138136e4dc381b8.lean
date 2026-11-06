import Mathlib

theorem number_theory_4818 :
  IsGreatest {a : ℤ | 0 < a ∧ ∀ n : ℕ, a ∣ 5^(n + 2) + 6^(2*n + 1)} 31 := by 
  constructor 
  · -- Show 31 is in the set
    constructor
    · norm_num 
    · -- Show that for all n: 31 divides 5^(n+2) + 6^(2n+1)
      intro n 
      have h1 : (31 : ℤ) ∣ 5 ^ (n + 2) + 6 ^ (2 * n + 1) := by 
        have h2 : ∀ (n : ℕ), (31 : ℤ) ∣ 5 ^ (n + 2) + 6 ^ (2 * n + 1) := by 
          intro n 
          induction n with 
          | zero =>
            norm_num 
          | succ k ih =>
            have h3 : (5 : ℤ) ^ ((k + 1) + 2) + 6 ^ (2 * (k + 1) + 1) = 5 * (5 ^ (k + 2)) + 36 * (6 ^ (2 * k + 1)) := by 
              ring_nf 
            rw [h3] 
            omega 
        specialize h2 n 
        simpa using h2 
      simpa using h1 
  · -- Show that 31 is greatest
    intro a ha 
    rcases ha with ⟨ha_pos, h⟩ 
    have h1 := h 0 
    norm_num at h1 
    have h2 : a ≤ 31 := by 
      apply Int.le_of_dvd (by norm_num) h1 
    linarith