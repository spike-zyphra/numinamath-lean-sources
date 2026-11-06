import Mathlib
import Aesop
open BigOperators Real Nat Topology Rat

/-Let $n=\frac{2^{2018}-1}{3}$ . Prove that $n$ divides $2^n-2$ .-/
theorem number_theory_8702 (n : ℕ) (h₀ : n = (2 ^ 2018 - 1) / 3) :n ∣ 2 ^ n - 2 := by
  have h1 : 2 ^ 2018  = 3 * n + 1:= by
    rw [h₀]
    ring
  --First of all, we have that $2 ^ {2018}  = 3n + 1$,
  have h2 : 2 ^ 2018 % n = 1 := by
    rw[h1]
    rw[add_mod]
    simp only [mul_mod_left, zero_add, dvd_refl, mod_mod_of_dvd]
    have g1 : n ≠ 1 := by
      by_contra t
      rw[t] at h1
      linarith
    exact one_mod_eq_one.mpr g1
  --then it is obvious that $2 ^ {2018} \equiv 1 \ (mod \ n)$.
  have h3 : 2 ^ n % n =  2 ^ (n % 2018) % n := by
  --Secondly, We want to prove that $2 ^ n \equiv 2 ^ r \ (mod \ n)$, where $r$ is the residue of $n$ when take modulo 2018.
    have g1 :  2 ^ (2018 * (n / 2018)) * 2 ^ (n % 2018) = 2 ^ n := by
      have t1 : 2018 * (n / 2018) + n % 2018 = n := by rw[mul_comm];apply div_add_mod'
      calc
      _ = 2 ^ (2018 * (n / 2018) + n % 2018) := by exact Eq.symm (Nat.pow_add 2 (2018 * (n / 2018)) (n % 2018))
      _ = _ := by rw[t1]
    rw[← g1]
    rw[pow_mul]
    have g2 : (2 ^ 2018) ^ (n / 2018) % n = 1 % n := by
      rw[pow_mod]
      rw[h2]
      simp only [one_pow]
    rw[mul_mod]
    rw[g2]
    simp only [mul_mod_mod, mod_mul_mod, one_mul]
  --That's right because $2 ^ {2018} \equiv 1 \ (mod \ n)$.
  --Further, $1009$ and $2$ is prime.
  have h4 : n % 1009 = 1 := by
    rw[h₀]
    ring
  --By FLT, we can get $n \equiv 1 \ (mod \ 1009)$
  have h5 : n % 2 = 1 := by
    rw[h₀]
    ring
  -- and $n \equiv 1 \ (mod \ 2)$.
  have h6: n % 2018 = 1 := by
    rw[h₀]
    ring
  --And that leads to $n \equiv 1 \ (mod \ 2018)$ by CRT,
  rw[h6] at h3
  simp at h3
  --implying that $r = 1$, so $2 ^ n \equiv 2 \ (mod \ n)$.
  have h7 : 2 ^ n % n = 2  := by
    rw[h3]
    rw[h₀]
    ring
  have h8 : 2 ^ n % n = 2 % n := by
    rw[h7]
    rw[h₀]
    ring
  rw[h8] at h7
  apply dvd_of_mod_eq_zero
  exact sub_mod_eq_zero_of_mod_eq h3
  --That's exactly $n \ | \ 2 ^ n - 2$, which is the conclusion.
