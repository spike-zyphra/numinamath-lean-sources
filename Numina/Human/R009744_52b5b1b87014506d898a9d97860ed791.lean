import Mathlib

/- 3.51 Prove that $N=\frac{5^{125}-1}{5^{25}-1}$ is not a prime number.
(33rd International Mathematical Olympiad Preliminary Problem, 1992) -/
theorem number_theory_114525 : ¬ Nat.Prime ((5^125 - 1) / (5^25 - 1)) := by
  --Put x = 5^25
  set x := 5^25
  --Show x^5 - 1) / (x - 1) = ((x^2 + 3 * x + 1) + 5^13 * (x + 1)) * ((x^2 + 3 * x + 1) - 5^13 * (x + 1)).
  have H0 : (x^5 - 1) / (x - 1) = ((x^2 + 3 * x + 1) + 5^13 * (x + 1)) * ((x^2 + 3 * x + 1) - 5^13 * (x + 1)) := by
    calc
      _ = x^4 + x^3 + x^2 + x + 1 := by ring
      _ = (x^2 + 3 * x + 1)^2 - 5 * x * (x + 1)^2 := by ring
      _ = (x^2 + 3 * x + 1)^2 - 5^26 * (x + 1)^2 := by ring
      _ = ((x^2 + 3 * x + 1) + 5^13 * (x + 1)) * ((x^2 + 3 * x + 1) - 5^13 * (x + 1)) := by ring
  --Show (x^2 + 3 * x + 1) + 5^13 * (x + 1) ≠ 1.
  have H1 : (x^2 + 3 * x + 1) + 5^13 * (x + 1) ≠ 1 := by
    omega
  --Show x ^ 2 + 3 * x + 1 - 5 ^ 13 * (x + 1) ≠ 1.
  have H12 : x ^ 2 + 3 * x + 1 - 5 ^ 13 * (x + 1) ≠ 1 := by
    norm_num
  --Show (x^2 + 3 * x + 1) - 5^13 * (x + 1) ≠ (x^5 - 1) / (x - 1).
  have H2 : (x^2 + 3 * x + 1) - 5^13 * (x + 1) ≠ (x^5 - 1) / (x - 1) := by
    have : (x^5 - 1) / (x - 1) = x^4 + x^3 + x^2 + x + 1 := by ring
    omega
  --Show (x^2 + 3 * x + 1) + 5^13 * (x + 1) ∣ (x^5 - 1) / (x - 1).
  have H3 : (x^2 + 3 * x + 1) + 5^13 * (x + 1) ∣ (x^5 - 1) / (x - 1) := by
    have : (x^5 - 1) / (x - 1) = ((x^2 + 3 * x + 1) + 5^13 * (x + 1)) * ((x^2 + 3 * x + 1) - 5^13 * (x + 1)) := by ring
    rw [this]
    use ((x^2 + 3 * x + 1) - 5^13 * (x + 1))
  --Show (x^5 - 1) / (x - 1) = ((x^2 + 3 * x + 1) + 5^13 * (x + 1)) * ((x^2 + 3 * x + 1) - 5^13 * (x + 1)).
  have H4 : (x^5 - 1) / (x - 1) = ((x^2 + 3 * x + 1) + 5^13 * (x + 1)) * ((x^2 + 3 * x + 1) - 5^13 * (x + 1)) := by ring
  --Show (x^5 - 1) / (x - 1) is not prime.
  have H41 : ¬ Nat.Prime ((x^5 - 1) / (x - 1)) := by
    apply Nat.not_prime_mul' H4.symm H1
    · exact H12
  --Show (x^5 - 1) / (x - 1) = (5 ^ 125 - 1) / (x - 1).
  have H42 : (x^5 - 1) / (x - 1) = (5 ^ 125 - 1) / (x - 1) := by norm_num
  rw [H42] at H41
  --Done.
  exact H41