import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat


/-
Jenn randomly chooses a number  $J$  from  $1, 2, 3,\ldots, 19, 20$ . Bela then randomly chooses a number  $B$  from  $1, 2, 3,\ldots, 19, 20$  distinct from  $J$ . The value of  $B - J$  is at least  $2$  with a probability that can be expressed in the form  $\frac{m}{n}$  where  $m$  and  $n$  are relatively prime positive integers. Find  $m+n$ .
-/

theorem number_theory_8799
    (m n : ℕ) (hn : n ≠ 0)
    (hmncop : m.Coprime n)
    (h : (m : ℚ) / n = ((∑ j in Finset.Icc 1 20, ∑ b in Finset.Icc 1 20, if b - j ≥ 2 then 1 else 0): ℚ) / (20 * 19)) :
    m + n = 29 := by

  -- by calculating, m / n equals 9 / 20
  rw [show (∑ j in Finset.Icc 1 20, ∑ b in Finset.Icc 1 20, if b - j ≥ 2 then (1 : ℚ) else 0) = 171 by native_decide,
      show (20 : ℚ) * 19 = 380 by norm_num,
      show (171 : ℚ) / 380 = 9 / 20 by norm_num] at h

  -- then we prove m = 9 and n = 20
  have heq : m * 20 = 9 * n := by
    qify
    refine mul_eq_mul_of_div_eq_div (m : ℚ) 9 (by norm_cast) (by norm_num) h

  have rm : 9 ∣ m := by
    have : 9 ∣ m * 20 := by
      rw [heq]
      exact Nat.dvd_mul_right 9 n
    exact Coprime.dvd_of_dvd_mul_right (show Nat.gcd 9 20 = 1 by norm_num) this
  obtain ⟨km, hkm⟩ := rm

  have rn : 20 ∣ n := by
    have : 20 ∣ 9 * n := by
      rw [← heq]
      exact Nat.dvd_mul_left 20 m
    exact Coprime.dvd_of_dvd_mul_left (show Nat.gcd 20 9 = 1 by norm_num) this
  obtain ⟨kn, hkn⟩ := rn

  have hkmeqkn: km = kn := by omega

  rw [hkm, hkn, hkmeqkn] at hmncop

  have := gcd_mul_of_coprime_of_dvd (Coprime.coprime_mul_right hmncop) (Nat.dvd_mul_left kn 20)
  rw [hmncop] at this

  -- thus m + n = 29
  omega
