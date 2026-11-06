import Mathlib

open Nat

/- When each of $702$, $787$, and $855$ is divided by the positive integer $m$, the remainder is always the positive integer $r$. When each of $412$, $722$, and $815$ is divided by the positive integer $n$, the remainder is always the positive integer $s \neq r$. Find $m+n+r+s$. -/
theorem number_theory_97032 (m n r s : ℕ) (hm : 0 < m) (hn : 0 < n) (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s) (hdiv : 702 % m = r ∧ 787 % m = r ∧ 855 % m = r) (hdiv' : 412 % n = s ∧ 722 % n = s ∧ 815 % n = s) : m + n + r + s = 62 := by
  -- Prove that m = 17
  have m_val : m = 17 := by
    rcases hdiv with ⟨h₁, h₂, h₃⟩
    -- m divides 85
    have m_dvd_85 : m ∣ 85 := by
      rw [← h₂] at h₁
      symm at h₁
      apply sub_mod_eq_zero_of_mod_eq at h₁
      norm_num at h₁
      rw [dvd_iff_mod_eq_zero]
      exact h₁
    -- m divides 68
    have m_dvd_68 : m ∣ 68 := by
      rw [← h₂] at h₃
      apply sub_mod_eq_zero_of_mod_eq at h₃
      norm_num at h₃
      rw [dvd_iff_mod_eq_zero]
      exact h₃
    -- Since m divides 85 and 68, m divides their gcd, namely 17.
    have m_dvd_17 : m ∣ 17 := by
      have : Nat.gcd 68 85 = 17 := by
        norm_num
      rw [← this]
      apply @Nat.dvd_gcd
      · exact m_dvd_68
      exact m_dvd_85
    have : m <= 17 := le_of_dvd (by positivity) m_dvd_17
    interval_cases m
    · rw [mod_one 702] at h₁
      linarith
    repeat omega
  -- Find the value of r by evaluating 702 mod m
  have r_val : r = 5 := by
    rw [m_val] at hdiv
    norm_num at hdiv
    exact symm hdiv
  have n_val : n = 31 := by
    rcases hdiv' with ⟨h₁, h₂, h₃⟩
    -- n divides 310
    have n_dvd_310 : n ∣ 310 := by
      rw [← h₂] at h₁
      symm at h₁
      apply sub_mod_eq_zero_of_mod_eq at h₁
      norm_num at h₁
      rw [dvd_iff_mod_eq_zero]
      exact h₁
    -- n divides 93
    have n_dvd_93 : n ∣ 93 := by
      rw [← h₂] at h₃
      apply sub_mod_eq_zero_of_mod_eq at h₃
      norm_num at h₃
      rw [dvd_iff_mod_eq_zero]
      exact h₃
    -- Since m divides 85 and 68, m divides their gcd, namely 31.
    have n_dvd_31 : n ∣ 31 := by
      have : Nat.gcd 310 93 = 31 := by
        norm_num
      rw [← this]
      apply @Nat.dvd_gcd
      · exact n_dvd_310
      exact n_dvd_93
    have : n <= 31 := le_of_dvd (by positivity) n_dvd_31
    interval_cases n
    · rw [mod_one] at h₁
      linarith
    repeat omega
  -- Find the value of s by evaluating 412 mod n
  have s_val : s = 9 := by
    rw [n_val] at hdiv'
    norm_num at hdiv'
    exact symm hdiv'
  -- Add the values together
  linarith