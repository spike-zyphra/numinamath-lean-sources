import Mathlib

/-Let $N_0 = 1000$. At a recent math contest, Evan was asked to find $2^{N_0} \pmod{p}$
for a given prime number $p$ with $100 < p < 500$. Evan has forgotten what the prime $p$ was,
but still remembers how he solved it: \begin{itemize} \item Evan first tried taking $N_0$ modulo $p - 1$,
but got a value $e$ larger than $100$. \item However, Evan noted that $e - \frac{1}{2}(p - 1) = 21$,
and then realized the answer was $-2^{21} \pmod{p}$. \end{itemize} What was the prime $p$?
Show that the prime $p$ was $179$.-/

theorem number_theory_635534 (N_0 p e: ℤ) (hp: Prime p) (h1: N_0 = 1000) (h2: 100 < p) (h3: p < 500)
  (h4: N_0 % (p - 1) = e) (h5: e > 100) (h6: e - (p - 1) / 2 = 21): p = 179 := by

  simp [h1] at *
  replace h6: 2 * e - (p - 1) = 42 := by
    qify
    qify at h6
    have u: ↑((p - 1) / 2) = ↑(p - 1) / (2: ℚ) := by
      apply Rat.intCast_div
      by_contra! o
      replace o: 2 ∣ p := by omega
      rw [← Int.natAbs_dvd_natAbs] at o
      simp at o
      rw [Nat.prime_dvd_prime_iff_eq] at o
      zify at o
      rw [show |p| = p by apply abs_of_nonneg (by omega)] at o
      simp [← o] at h2
      norm_num
      rw [← Int.prime_iff_natAbs_prime]
      tauto
    rw [u] at h6
    clear *- h6
    field_simp at h6
    linarith
  replace h4: 2 * e = 2 * (1000 % (p - 1)) := by
    rw [← h4]
  replace h6: 2 * e = p - 1 + 42 := by
    nlinarith
  rw [h6] at h4
  replace h4: (p - 1 + 42) % (p - 1) = (2 * (1000 % (p - 1))) % (p - 1) := by
    rw [h4]
  have f1: (p - 1 + 42) % (p - 1) = 42 % (p - 1) := by
    rw [Int.add_emod]
    simp
  have f2: (2 * (1000 % (p - 1))) % (p - 1) = 2000 % (p - 1) := by
    rw [Int.mul_emod]
    have f: 1000 % (p - 1) % (p - 1) = 1000 % (p - 1) := by
      apply Int.emod_emod
    rw [f]
    rw [← Int.mul_emod]
    simp
  rw [f1, f2] at h4
  clear f1 f2
  replace h4: 1958 % (p - 1) = 0 := by
    rw [show (1958: ℤ) = 2000 - 42 by omega]
    rw [Int.sub_emod]
    simp [h4]
  apply Int.dvd_of_emod_eq_zero at h4
  have g: (p - 1).natAbs ∈ Nat.divisors 1958 := by
    simp
    rw [← Int.natAbs_dvd_natAbs] at h4
    simp at h4
    tauto
  rw [show Nat.divisors 1958 = {1, 2, 11, 22, 89, 178, 979, 1958} by native_decide] at g
  simp at g
  zify at g
  rw [show |p - 1| = p - 1 by apply abs_of_nonneg (by omega)] at g
  clear h4 h6 h5 h1
  rcases g with g | g | g | g | g | g | g | g
  all_goals omega