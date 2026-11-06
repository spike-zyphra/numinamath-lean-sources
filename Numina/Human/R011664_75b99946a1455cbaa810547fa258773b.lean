import Mathlib

/- Let $a$, $b$, and $c$ be non-zero real number such that $\tfrac{ab}{a+b}=3$, $\tfrac{bc}{b+c}=4$, and $\tfrac{ca}{c+a}=5$. There are relatively prime positive integers $m$ and $n$ so that $\tfrac{abc}{ab+bc+ca}=\tfrac{m}{n}$. Find $m+n$. -/
theorem algebra_44175 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a * b / (a + b) = 3) (h2 : b * c / (b + c) = 4) (h3 : c * a / (c + a) = 5)
    (m n : ℕ) (hm : m > 0) (hn : n > 0) (hmn : Nat.Coprime m n)
    (hmeq : a * b * c / (a * b + b * c + c * a) = m / n) :
    m + n = 167 := by 
  have eq1 : a * b / (a + b) = 1 / (1 / a + 1 / b) := by 
    field_simp
    ring_nf
  have eq2 : b * c / (b + c) = 1 / (1 / b + 1 / c) := by
    field_simp
    ring_nf
  have eq3 : c * a / (c + a) = 1 / (1 / c + 1 / a) := by
    field_simp 
    ring_nf
  rw [eq1] at h1
  rw [eq2] at h2
  rw [eq3] at h3
  have eq4 : (1 / a + 1 / b) = 1 / 3 := by 
    rw [←h1]
    simp
  have eq5 : (1 / b + 1 / c) = 1 / 4 := by
    rw [←h2]
    simp
  have eq6 : (1 / c + 1 / a) = 1 / 5 := by
    rw [←h3]
    simp
  -- Simplify fractions involving a, b, and c.
  have eq7 : 1 / a + 1/ b + 1 / c = 47 / 120 := by 
    linarith
  have eq8 : a * b * c / (a * b + b * c + c * a) = 1 / (1 / a + 1/ b + 1 / c) := by
    field_simp
    ring_nf
  rw [eq8, eq7] at hmeq
  simp at hmeq
  have meq : m = 120 := by 
    field_simp at hmeq
    norm_cast at hmeq
    have mdvd : m ∣ 120 * n := by 
      rw [hmeq]
      simp
    have mdvd2 : m ∣ 120 := by
      exact Nat.Coprime.dvd_of_dvd_mul_right hmn mdvd
    have dvd1 : 120 ∣ m * 47 := by 
      rw [← hmeq]
      simp
    have dvd2 : Nat.Coprime 120 47 := by 
      norm_num
    have dvd3 : 120 ∣ m := by 
      exact Nat.Coprime.dvd_of_dvd_mul_right dvd2 dvd1
    exact Nat.dvd_antisymm mdvd2 dvd3
  have neq : n = 47 := by
    field_simp at hmeq
    rw [meq] at hmeq
    norm_cast at hmeq
    linarith
  rw [meq, neq]