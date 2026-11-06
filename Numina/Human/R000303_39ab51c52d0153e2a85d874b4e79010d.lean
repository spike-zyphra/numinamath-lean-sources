import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- For each positive integer  $ n$ , let  $ f(n)$  denote the greatest common divisor of
 $ n!\plus{}1$  and  $ (n\plus{}1)!$ . Find, without proof, a formula for  $ f(n)$ .-/
theorem number_theory_8861 :
  ∀ n : ℕ, n > 0 → Nat.gcd (n ! + 1) (n + 1)! = ite (n+1).Prime (n + 1) 1 := by
    intro n npos
    by_cases h : (n + 1).Prime <;> simp [h]
    -- Case 1: \( n+1 \) is a prime number
    · have h1 : Nat.gcd (n ! + 1) n ! = 1 := by
        refine coprime_self_add_left.mpr ?_
        exact Nat.gcd_one_left n !
      -- Since \( \gcd(n!, n! + 1) = 1 \), the GCD simplifies to:
      -- \[
      -- f(n) = \gcd(n! + 1, n+1)
      -- \]
      rw [Nat.factorial_succ, Nat.Coprime.gcd_mul_right_cancel_right]
      refine gcd_eq_right ?_
      -- By Wilson's Theorem, for a prime number \( p \), we have:
      -- \[
      -- (p-1)! \equiv -1 \pmod{p}
      -- \]
      have := (Nat.prime_iff_fac_equiv_neg_one (show n + 1 ≠ 1 by omega)).1 h
      simp at this
      -- Applying this to our problem, if \( n+1 \) is prime, then:
      -- \[
      -- n! \equiv -1 \pmod{n+1}
      -- \]
      have := (ZMod.natCast_eq_iff _ _ _ ).1 this
      -- This implies that \( n! + 1 \) is divisible by \( n+1 \). Since \( (n+1)! = (n+1) \cdot n! \), it follows that:
      -- \[
      -- \gcd(n! + 1, (n+1)!) = \gcd(n! + 1, (n+1) \cdot n!) = n+1
      -- \]
      rw [ZMod.val_neg_one ] at this
      obtain ⟨k, hk⟩ := this
      rw [hk]
      exact ⟨k + 1, by linarith⟩
      exact coprime_comm.mp h1
    -- Case 2: \( n+1 \) is not a prime number.
    · by_contra!
      obtain ⟨m, hm⟩ := Nat.exists_prime_and_dvd this
      have h1 := Nat.dvd_gcd_iff.1 hm.2
      have h2 := (Nat.Prime.dvd_factorial hm.1).1 h1.2
      have h3 : m ≠ n + 1 := fun tmp => h (tmp ▸ hm.1)
      -- If \( n+1 \) is not a prime number, then all prime factors of \( n+1 \) are less
      -- than or equal to \( n \). This means that these prime factors divide \( n! \).
      have h4 : m ∣ n ! := (Nat.Prime.dvd_factorial hm.1).2 (by omega)
      --  This implies that \( n! + 1 \) is relatively prime to \( n+1 \). Since \( (n+1)! = (n+1) \cdot n! \), it follows that:
      -- \[
      -- \gcd(n! + 1, (n+1)!) = \gcd(n! + 1, (n+1) \cdot n!) = 1
      -- \]
      have h5 : m ∣ 1 := by
        convert Nat.dvd_sub (by omega) h1.1 h4
        omega
      replace h5 := Nat.le_of_dvd (by simp) h5
      have h6 : 2 ≤ m := Prime.two_le hm.1
      linarith
