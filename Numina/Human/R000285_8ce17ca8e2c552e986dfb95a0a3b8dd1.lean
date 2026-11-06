import Mathlib


/-
When each of $702$, $787$, and $855$ is divided by the positive integer $m$, the remainder is always the positive integer $r$. When each of $412$, $722$, and $815$ is divided by the positive integer $n$, the remainder is always the positive integer  $s \neq r$ . Fine  $m+n+r+s$ .
-/

theorem number_theory_8821
    (m n r s : ℕ)
    (h₀ : 0 < m)
    (h₁ : 0 < n)
    (h₂ : 0 < r)
    (h₃ : 0 < s)
    (h₄ : ∀ x ∈ ({702, 787, 855} : Finset ℕ), x % m = r)
    (h₅ : ∀ x ∈ ({412, 722, 815} : Finset ℕ), x % n = s)
    (h₆ : r ≠ s) :
    m + n + r + s = 62 := by

  -- For the first set of numbers (702, 787, 855) divided by $ m $ with remainder $ r $:
  have h1 : m = 17 ∧ r = 5 := by
    -- We have:
    have r1 := h₄ 702 (by simp)
    have r2 := h₄ 787 (by simp)
    have r3 := h₄ 855 (by simp)
    zify at r1 r2 r3
    -- Subtracting the first from the second and the second from the third:
    have r4 : m ∣ 85 := by
      zify
      have := Int.sub_emod 787 702 (m : ℤ)
      simp_all
    have r5 : m ∣ 68 := by
      zify
      have := Int.sub_emod 855 787 (m : ℤ)
      simp_all
    -- Thus, $ m $ must divide both 85 and 68. The greatest common divisor (gcd) of 85 and 68 is 17. Therefore, $ m = 17 $.
    have : m ∣ 17 := Nat.dvd_gcd r4 r5
    rcases (Nat.dvd_prime (show Nat.Prime 17 by norm_num)).mp this with h | h
    . linarith [show r = 0 by simp_all] -- if m = 1, then r = 0, contradict to 0 < r
    rw [h] at r1
    norm_num at r1
    norm_cast at r1
    exact ⟨h, r1.symm⟩


  -- For the second set of numbers (412, 722, 815) divided by $ n $ with remainder $ s $:
  have h2 : n = 31 ∧ s = 9 := by
    -- We have:
    have r1 := h₅ 412 (by simp)
    have r2 := h₅ 722 (by simp)
    have r3 := h₅ 815 (by simp)
    zify at r1 r2 r3
    -- Subtracting the first from the second and the second from the third:
    have r4 : n ∣ 310 := by
      zify
      have := Int.sub_emod 722 412 (n : ℤ)
      simp_all
    have r5 : n ∣ 93 := by
      zify
      have := Int.sub_emod 815 722 (n : ℤ)
      simp_all
    -- 1. Thus, $ n $ must divide both 310 and 93. The gcd of 310 and 93 is 31. Therefore, $ n = 31 $.
    have : n ∣ 31 := Nat.dvd_gcd r4 r5
    rcases (Nat.dvd_prime (show Nat.Prime 31 by norm_num)).mp this with h | h
    . linarith [show s = 0 by simp_all] -- if n = 1, then s = 0, contradict to 0 < s
    rw [h] at r1
    norm_num at r1
    norm_cast at r1
    exact ⟨h, r1.symm⟩

  -- Finally, adding all the values:
  linarith
