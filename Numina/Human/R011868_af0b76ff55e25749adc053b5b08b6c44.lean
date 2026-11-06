import Mathlib

theorem number_theory_156842 :
    IsGreatest {d | ∀ n : ℤ, d ∣ n^5 - n} 30 := by
  constructor
  · intro n
    have h1 : n ^ 5 % 30 = n % 30 := by
      have h2 : n ^ 5 % 2 = n % 2 := by
        have h2 : n % 2 = 0 ∨ n % 2 = 1 := by
          omega
        rcases h2 with (h2 | h2)
        · simp [h2, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        · simp [h2, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      have h3 : n ^ 5 % 3 = n % 3 := by
        have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
          omega
        rcases h3 with (h3 | h3 | h3)
        · simp [h3, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        · simp [h3, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        · simp [h3, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      have h5 : n ^ 5 % 5 = n % 5 := by
        have h5 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
          omega
        rcases h5 with (h5 | h5 | h5 | h5 | h5)
        · simp [h5, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        · simp [h5, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        · simp [h5, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        · simp [h5, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        · simp [h5, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      have h30 : n ^ 5 % 30 = n % 30 := by
        have h301 : n ^ 5 % 2 = n % 2 := h2
        have h302 : n ^ 5 % 3 = n % 3 := h3
        have h303 : n ^ 5 % 5 = n % 5 := h5
        have h : n ^ 5 % 30 = n % 30 := by
          omega
        exact h
      exact h30
    have h2 : 30 ∣ n ^ 5 - n := by
      omega
    exact h2
  · -- Now we show that 30 is the greatest such integer by proving any divisor of $n^5 - n$ for all $n$ must be ≤ 30.
    intro d hd
    have h1 := hd 2
    have h2 := hd 3
    have h3 := hd 5
    norm_num at h1 h2 h3
    have : d ∣ 30 := by
      exact Int.dvd_gcd h1 h2
    have : d ≤ 30 := by
      exact Int.le_of_dvd (by norm_num) this
    exact this