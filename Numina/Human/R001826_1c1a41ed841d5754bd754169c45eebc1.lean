import Mathlib

/- Let $f(x) = x^2 + x + 1$. Determine the ordered pair $(p,q)$ of primes satisfying $f(p) = f(q) + 242$.

[i]2016 CCA Math Bonanza #8[/i] -/
theorem number_theory_37760 {p q : ℤ} (hp : Prime p) (hq : Prime q)
  (ppos : p > 0) (qpos : q > 0)
  (h : p^2 + p + 1 = q^2 + q + 1 + 242) :
  (p, q) = (61, 59) := by 
  have eq1 : (p - q)* (p + q + 1) = 242 := by linarith
  have eq2 : (242 : ℤ) = 2* 11 * 11 := by norm_num
  have pq_pos : p - q > 0 := by nlinarith
  have ineq1 : p - q < p + q + 1 := by linarith
  have dvd1 : p - q ∣ 242 := by 
    rw [←eq1]
    simp
  have ple : p - q < 16 := by nlinarith
  have peq : p - q = 1 ∨ p - q = 2 ∨ p - q = 11 := by 
    interval_cases p - q 
    simp
    simp
    norm_num at dvd1
    norm_num at dvd1
    norm_num at dvd1
    norm_num at dvd1
    norm_num at dvd1
    norm_num at dvd1
    norm_num at dvd1
    norm_num at dvd1
    simp
    norm_num at dvd1
    norm_num at dvd1
    norm_num at dvd1
    norm_num at dvd1
  obtain hpeq | hpeq | hpeq := peq
  have h' : p + q + 1 = 242 := by nlinarith
  have peq' : p = 121 := by linarith
  rw [peq'] at hp
  norm_num at hp
  have q_eq : q = 59 := by nlinarith
  rw [q_eq] at hpeq
  simp_all
  linarith
  have h :  p + q + 1 = 22 := by nlinarith
  have qeq : q = 5 := by linarith
  have peq : p = 16 := by linarith
  rw [peq] at hp
  norm_num at hp