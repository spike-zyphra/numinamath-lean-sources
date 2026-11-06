import Mathlib

/-
Let $k$ be an integer. Let $a, b, c, d$ be integers such that $a d-b c=k$ and $a c+b d \neq 0$. Prove that $\gcd(a^2+b^2, ac+bd)$ divides $|k|\gcd(a,b)$.
-/

theorem number_theory_637811 (k a b c d : Int) (h1: a*d - b*c = k) (h2: a * c + b * d ≠ 0):
((Int.gcd (a^2+b^2) (a*c+b*d)):ℤ) ∣ (|k| * (Int.gcd a b)) := by
  --Let r = (a²+b², ac+bd).
  let r := ((Int.gcd (a^2+b^2) (a*c+b*d)):ℤ)

  have h3 : r ∣ a^2+b^2 := by exact Int.gcd_dvd_left
  have h4 : r ∣ a*c+b*d := by exact Int.gcd_dvd_right

  --Then, by assumption, we have r ∣  d*(a²+b²) and r ∣ b*(ac+bd).
  have t1: r ∣ (k*a) := by 
    have l1 : r ∣ d * (a^2+b^2) := by exact Dvd.dvd.mul_left h3 d
    have l2 : r ∣ b * (a*c+b*d) := by exact Dvd.dvd.mul_left h4 b
    have l3 : r ∣ d * (a^2+b^2) - b * (a*c+b*d) := by exact Int.dvd_sub l1 l2
    --Note that d*(a²+b²) - b*(ac+bd) = ka. Hence, we have r ∣ ka.
    have : d * (a^2+b^2) - b * (a*c+b*d) = k*a := by rw [← h1]; ring
    rw [this] at l3
    exact l3
  --Similarly, we can get r ∣ kb.
  have t2: r ∣ (k*b) := by 
    have l1 : r ∣ c * (a^2+b^2) := by exact Dvd.dvd.mul_left h3 c
    have l2 : r ∣ a* (a*c+b*d) := by exact Dvd.dvd.mul_left h4 a
    have l3 : r ∣ a * (a*c+b*d) - c * (a^2+b^2) := by exact Int.dvd_sub l2 l1
    have : a * (a*c+b*d) - c * (a^2+b^2) = k*b := by rw [← h1]; ring
    rw [this] at l3
    exact l3
  --Hence, r ∣ gcd (ka,kb) = |k|gcd(a,b).
  have t3: r ∣ (Int.gcd (k*a) (k*b)) := by exact Int.dvd_gcd t1 t2
  have : (Int.gcd (k*a) (k*b)) = k.natAbs * Int.gcd a b := by rw [Int.gcd_mul_left]
  simp [this] at t3
  exact t3
