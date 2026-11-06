import Mathlib

open Nat

/- 3.26. Prove that for infinitely many primes $p$, the equation $x^{2}+x+1=p y$ has integer solutions $(x, y)$.
-/
theorem number_theory_167802 :
    ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n ∧ ∃ x y : ℤ, x^2 + x + 1 = p * y := by
  rintro n
  -- consider minimal factor of n!^2 + n! + 1
  let p := minFac (n ! ^2 + n ! + 1)
  use p
  -- it divides n!^2 + n! + 1, and is a prime
  have hm := minFac_dvd (n ! ^2 + n ! + 1)
  have h1 : n ! ^2 + n ! + 1 ≠ 1 := by
    have : 0 < n ! := by exact factorial_pos n
    omega
  have hm' : Nat.Prime p := minFac_prime h1
  and_intros
  -- it is a prime obviously
  . exact hm'
  -- it is > n, otherwise p ≤ n implies p ∣ n!^2 + n! which means p ∣ 1 impossible
  . by_contra hpn
    simp at hpn
    have h₁ : p ∣ n ! ^ 2 + n ! + 1 := by exact hm
    have h₂ : p ∣ n ! := by
      exact (Prime.dvd_factorial hm').mpr hpn
    have h₃ : p ∣ n ! ^ 2 := by
      refine dvd_pow h₂ (by norm_num)
    have h₄ : p ∣ n ! ^ 2 + n ! := by
      exact (Nat.dvd_add_iff_right h₃).mp h₂
    have h₅ : p ∣ 1 := by
      exact (Nat.dvd_add_iff_right h₄).mpr hm
    exact hm'.not_dvd_one h₅
  -- we can use x = n!, y = (n!^2 + n! + 1)/p
  . obtain ⟨k, hk⟩ := hm
    use n !, k
    norm_cast