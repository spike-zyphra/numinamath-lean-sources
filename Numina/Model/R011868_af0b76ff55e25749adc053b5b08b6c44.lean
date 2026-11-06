import Mathlib

theorem number_theory_156842 :
    IsGreatest {d | ∀ n : ℤ, d ∣ n^5 - n} 30 := by
  constructor
  · -- Show that 30 divides $n^5 -n$ for all integers $n$.
    intro n
    have h1 : (n ^ 5 - n) % 2 = 0 := by
      have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases h with (h | h)
      · -- Case where $n$ is even
        simp [pow_succ, Int.sub_emod, h, Int.mul_emod]
      · -- Case where $n$ is odd
        simp [pow_succ, Int.sub_emod, h, Int.mul_emod]
    have h2 : (n ^ 5 - n) % 3 = 0 := by
      have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h with (h | h | h)
      · -- Case where $n ≡ 0$
        simp [pow_succ, Int.sub_emod, h, Int.mul_emod]
      · -- Case where $n ≡ 1$
        simp [pow_succ, Int.sub_emod, h, Int.mul_emod]
      · -- Case where $n ≡ 2$
        simp [pow_succ, Int.sub_emod, h, Int.mul_emod]
    have h3 : (n ^ 5 - n) % 5 = 0 := by
      have h : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
      rcases h with (h | h | h | h | h)
      · -- Case where $n ≡ 0$
        simp [pow_succ, Int.sub_emod, h, Int.mul_emod]
      · -- Case where $n ≡ 1$
        simp [pow_succ, Int.sub_emod, h, Int.mul_emod]
      · -- Case where $n ≡ 2$
        simp [pow_succ, Int.sub_emod, h, Int.mul_emod]
      · -- Case where $n ≡ 3$
        simp [pow_succ, Int.sub_emod, h, Int.mul_emod]
      · -- Case where $n ≡ 4$
        simp [pow_succ, Int.sub_emod, h, Int.mul_emod]
    have h4 : 30 ∣ n ^ 5 - n := by 
      omega
    exact h4
  · -- Show that $30$ is greatest such integer.
    intro d h
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    have h6 := h 6
    have h7 := h 10
    have h8 := h (-1)
    have h9 := h (-2)
    norm_num at h2 h3 h4 h5 h6 h7 h8 h9
    have h10 : d ∣ 30 := by 
      exact Int.dvd_gcd (Int.dvd_gcd (h2) (h3)) (h9)
    have h11 : d ≤ 30 := by 
      apply Int.le_of_dvd (by norm_num) h10
    linarith