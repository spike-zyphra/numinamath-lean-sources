import Mathlib

open Nat

/-- Auxiliary lemma : $\frac {(2*(k+1))!} {(k+1)!} = 2 * (2 * k + 1) * (2 * k) ! / k !$ -/
lemma aux_4067 (k : ℕ) :  (2 * (k + 1))! / (k + 1)! = 2 * (2 * k + 1) * (2 * k) ! / k ! := by
  have h2 : k + 1 ∣ (2 * k + 2) * (2 * k + 1) := by
        apply dvd_mul_of_dvd_left
        rw [show (2 * k + 2 = 2 * (k + 1)) by linarith]
        exact dvd_mul_of_dvd_right (Nat.dvd_refl (k + 1)) 2
  calc
    _ = (2 * k + 2)! / (k + 1)! := by ring_nf
    _ = (2 * k + 2) * (2 * k + 1) * (2 * k)! / ((k + 1) * (k)!) := by
      rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
      congr 1; ring
    _ = (2 * k + 2) * (2 * k + 1) / (k + 1) * (2 * k)! / (k)! := by
      have h1 : k ! ∣ (2 * k)! := factorial_dvd_factorial (by linarith)
      rw [Nat.mul_div_mul_comm h2 h1, ←Nat.mul_div_assoc _ h1]
  congr
  rw [show (2 * k + 2 = 2 * (k + 1)) by linarith]
  have h3 : 0 < k + 1 := by simp
  have h1 : k + 1 ∣ 2 * (k + 1) * (2 * k + 1) := by
    convert h2 using 1
  have := Nat.div_eq_iff_eq_mul_left h3 h1 (c := 2 * (2 * k + 1))
  rw [Nat.div_eq_iff_eq_mul_left h3 h1 (c := 2 * (2 * k + 1)) ]
  ring

/-- Prove that the number $\( N_k = \frac{(2k)!}{k!} \)$ is divisible by $\( 2^k \)$ and not divisible by $\( 2^{k+1} \)$.-/
theorem number_theory_4067 (k : ℕ) : 2 ^ k ∣ (2 * k) ! / k ! ∧ ¬2 ^ (k + 1) ∣ (2 * k) ! / k ! := by
  -- induction on k
  induction' k with k hk
  · -- when $k=1$, this is easy to prove.
    simp
  · -- assume the statement is true for some $k=n$.
    rw [aux_4067 k]
    constructor
    · rw [Nat.pow_add_one, mul_comm, Nat.mul_div_assoc _ (factorial_dvd_factorial (by linarith))]
      refine Nat.mul_dvd_mul (by simp) hk.1
    · rw [Nat.pow_add_one, mul_comm]
      intro h
      rw [mul_assoc, Nat.mul_div_assoc] at h
      have h1 := (Nat.dvd_of_mul_dvd_mul_left (by simp) h)
      have : 2 ^ (k + 1) ∣ (2 * k)! / k ! := by
        have : ¬ 2 ∣ (2 * k + 1) := by simp
        rw [ Nat.mul_div_assoc] at h1
        exact Prime.pow_dvd_of_dvd_mul_left (Nat.prime_iff.1 Nat.prime_two) (k + 1) this h1
        exact (factorial_dvd_factorial (by linarith))
      exact hk.2 this
      exact dvd_mul_of_dvd_right (factorial_dvd_factorial (by linarith)) (2 * k + 1)
