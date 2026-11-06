import Mathlib

theorem number_theory_285295 : IsGreatest {n | ∀ a : ℤ, n ∣ a^5 - a} 30 := by
  constructor
  · -- Show that 30 is in the set.
    intro a
    -- Let's prove that 30 divides $a^5 - a$ for all integers $a$.
    -- First consider modulo 2.
    have h1 : a^5 % 2 = a % 2 := by
      have h2 : a % 2 = 0 ∨ a % 2 = 1 := by
        omega
      rcases h2 with (h2 | h2)
      · -- case a even
        simp [pow_succ, Int.mul_emod, h2]
      · -- case a odd
        simp [pow_succ, Int.mul_emod, h2]
    -- Then modulo 3.
    have h2 : a^5 % 3 = a % 3 := by
      have h3 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by
        omega
      rcases h3 with (h3 | h3 | h3)
      · -- case a ≡ 0
        simp [pow_succ, Int.mul_emod, h3]
      · -- case a ≡ 1
        simp [pow_succ, Int.mul_emod, h3]
      · -- case a ≡ 2
        simp [pow_succ, Int.mul_emod, h3]
    -- Then modulo 5.
    have h3 : a^5 % 5 = a % 5 := by
      have h4 : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by
        omega
      rcases h4 with (h4 | h4 | h4 | h4 | h4)
      · -- case a ≡ 0
        simp [pow_succ, Int.mul_emod, h4]
      · -- case a ≡ 1
        simp [pow_succ, Int.mul_emod, h4]
      · -- case a ≡ 2
        simp [pow_succ, Int.mul_emod, h4]
      · -- case a ≡ 3
        simp [pow_succ, Int.mul_emod, h4]
      · -- case a ≡ 4
        simp [pow_succ, Int.mul_emod, h4]
    -- Now combine them using the Chinese remainder theorem.
    have h4 : (a^5 - a) % 30 = 0 := by
      -- Show that a^5 ≡ a (mod 2).
      have h1' : a^5 % 2 = a % 2 := h1
      -- Show that a^5 ≡ a (mod 3).
      have h2' : a^5 % 3 = a % 3 := h2
      -- Show that a^5 ≡ a (mod 5).
      have h3' : a^5 % 5 = a % 5 := h3
      -- Hence, a^5 ≡ a (mod 30).
      omega
    exact Int.dvd_of_emod_eq_zero h4
  · -- Show that if n is in the set, then n ≤ 30.
    rintro n hn
    have h1 := hn 2
    norm_num at h1
    have h6 : n ≤ 30 := by
      apply Int.le_of_dvd (by norm_num) h1
    linarith