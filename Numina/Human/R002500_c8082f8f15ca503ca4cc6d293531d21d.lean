import Mathlib
open Mathlib
/-- The positive integers $A, B, A-B,$ and $A+B$ are all prime numbers. The sum of these four primes is

$\mathrm{(A)}\ \mathrm{even} \qquad\mathrm{(B)}\ \mathrm{divisible\ by\ }3 \qquad\mathrm{(C)}\ \mathrm{divisible\ by\ }5 \qquad\mathrm{(D)}\ \mathrm{divisible\ by\ }7 \qquad\mathrm{(E)}\ \mathrm{prime}$ -/
theorem number_theory_94304 (A B : ℕ) (hA : A.Prime) (hB : B.Prime)
(hA_diff_B : (A - B).Prime) (hA_add_B : (A + B).Prime) :
A + B + (A - B) + (A + B) = 17 := by
  -- https://artofproblemsolving.com/wiki/index.php/2002_AMC_12B_Problems/Problem_11
  have js : A - B > 0 := Nat.Prime.pos hA_diff_B
  have ma : A > B := by exact Nat.lt_of_sub_pos js
  -- B might be 2
  by_cases mm : B = 2
  · subst B
    zify [js, ma]
    ring_nf
    obtain rfl | dkw : A = 2 ∨ Odd A := by exact Nat.Prime.eq_two_or_odd' hA
    -- A can't be 2
    · norm_num at ma
    -- A is odd
    · -- try A from 3 to 5. 5 fits
      (obtain a | a | a | a : A = 3 ∨ A = 4 ∨ A = 5 ∨ 6 ≤ A := by omega) <;> try (subst A; norm_num at *)
      -- now 6 ≤ A. we have to arrive at a contradiction
      -- split n into 4 cases
      have pri6 (n : ℕ) (f : Nat.Prime n) : n = 2 ∨ n = 3 ∨ n % 6 = 1 ∨ n % 6 = 5 := by
        clear * - f
        -- consider all n < 7
        (obtain z | z | z | z | z | z | z | z : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ 7 ≤ n := by omega) <;> try (subst n; norm_num at *)
        have kw := Nat.mod_lt n (by decide : 0 < 6)
        have kk : n = 6 * (n / 6) + (n % 6) := by exact Eq.symm (Nat.div_add_mod n 6)
        -- consider all possible remainders
        (obtain d | d | d | d | d | d : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega) <;> try tauto
        -- remainder 0: n not prime
        · have wk : 6 ∣ n := by exact Nat.dvd_of_mod_eq_zero d
          have kk := Nat.not_prime_of_dvd_of_lt wk (by decide) (by linarith)
          tauto
        -- remainder 2: n not prime
        · have kw : n = 2 * (3 * (n / 6) + 1) := by linarith
          have wk : 2 ∣ n := by exact Dvd.intro (3 * (n / 6) + 1) (id (Eq.symm kw))
          have kk := Nat.not_prime_of_dvd_of_lt wk (by decide) (by linarith)
          tauto
        -- remainder 3: n not prime
        · have kw : n = 3 * (2 * (n / 6) + 1) := by linarith
          have wk : 3 ∣ n := by exact Dvd.intro (2 * (n / 6) + 1) (id (Eq.symm kw))
          have kk := Nat.not_prime_of_dvd_of_lt wk (by decide) (by linarith)
          tauto
        -- remainder 4: n not prime
        · have kw : n = 2 * (3 * (n / 6) + 2) := by linarith
          have wk : 2 ∣ n := by exact Dvd.intro (3 * (n / 6) + 2) (id (Eq.symm kw))
          have kk := Nat.not_prime_of_dvd_of_lt wk (by decide) (by linarith)
          tauto
      -- possible remainders of A when divided by 6
      obtain rfl | rfl | jd := pri6 A (by assumption) <;> try norm_num at *
      -- possible remainders of A - 2
      obtain je | je | je := pri6 (A - 2) (by assumption)
      · have mm : A = 4 := by omega
        subst A
        norm_num at *
      · have mm : A = 5 := by omega
        subst A
        norm_num at *
      -- possible remainders of A + 2
      obtain jf | jf | jf := pri6 (A + 2) (by assumption)
      · have mm : A = 0 := by omega
        subst A
        norm_num at *
      · have mm : A = 2 := by omega
        subst A
        norm_num at *
      -- contradiction
      omega
  · obtain rfl | dkw : B = 2 ∨ Odd B := by exact Nat.Prime.eq_two_or_odd' hB
    · norm_num at mm
    -- B is odd
    -- let's see if A can be 2
    obtain rfl | dw : A = 2 ∨ Odd A := by exact Nat.Prime.eq_two_or_odd' hA
    -- no
    · (obtain a | a : B = 0 ∨ B = 1 := by omega) <;> subst B <;> norm_num at *
    -- A is odd
    obtain kw | kw : A + B = 2 ∨ Odd (A + B) := by exact Nat.Prime.eq_two_or_odd' hA_add_B
    -- what if A + B = 2?
    · have kss : A = 1 ∨ A = 2 := by omega
      have kdd : B = 0 ∨ B = 1 := by omega
      obtain kss | kss := kss <;> obtain kdd | kdd := kdd <;> subst A <;> subst B <;> norm_num at *
      -- impossible
    -- A + B is odd
    · have ke : Even (A + B) := by exact Odd.add_odd dw dkw
      have kw : ¬Odd (A + B) := by exact Nat.not_odd_iff_even.mpr ke
      -- contradiction
      tauto