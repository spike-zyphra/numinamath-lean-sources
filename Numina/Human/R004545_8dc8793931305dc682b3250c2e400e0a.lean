import Mathlib

/- 2. 92 The largest even number that cannot be expressed as the sum of two odd composite numbers is?

-/
theorem number_theory_281683 :
    IsGreatest {n | Even n ∧ ¬∃ a b, Odd a ∧ Odd b ∧ a + b = n ∧ ¬Nat.Prime a ∧ ¬Nat.Prime b ∧ a ≠ 1 ∧ b ≠ 1} 38 := by
  constructor
  -- first we show 38 is in the set
  . simp
    and_intros
    . decide
      -- consider all possible value of a, they belong to 0..38, y is 38 - y, we can norm_num at the primality, even value to find all cases create contradiction
    . rintro x hx y hy hxy hpx hpy hx1
      by_contra hy1
      have : x ≤ 38 := by linarith
      replace hxy : y = 38 - x := by omega
      rw [hxy] at hy1 hpy hy
      clear hxy
      rw [Nat.odd_iff] at hx hy
      interval_cases x
      all_goals norm_num at hx hy hpx hpy
  -- now we show if not possible then n <= 38, we do the contrapositive that if 38 < n then n has dcomposition of two odd composites
  . rintro n ⟨hn, habn⟩
    contrapose habn
    simp at habn ⊢
    have hn' := hn
    rw [Nat.even_iff] at hn
    -- we will casework  on n % 10
    have : n % 10 < 10 := Nat.mod_lt n (by norm_num)
    set a := n / 10
    interval_cases h : n % 10
    -- first we handle the cases where remainder is odd
    any_goals (
      rw [← Nat.mod_mod_of_dvd _ (show 2 ∣ 10 by norm_num), h] at hn
      norm_num at hn
    )
    -- for remainder 0, n = 25 + 5k
    . use 25
      norm_num
      and_intros
      . decide
      . use n - 25
        and_intros
        . apply Nat.Even.sub_odd (by omega) hn' (by decide)
        . omega
        . apply Nat.not_prime_mul' (a := 5) (b := (n - 25)/5) (by omega) (by norm_num) (by omega)
        . omega
    -- for remainder 2, n = 27 + 5k
    . use 27
      norm_num
      and_intros
      . decide
      . use n - 27
        and_intros
        . apply Nat.Even.sub_odd (by omega) hn' (by decide)
        . omega
        . apply Nat.not_prime_mul' (a := 5) (b := (n - 27)/5) (by omega) (by norm_num) (by omega)
        . omega
    -- for remainder 4, n = 9 + 5k
    . use 9
      norm_num
      and_intros
      . decide
      . use n - 9
        and_intros
        . apply Nat.Even.sub_odd (by omega) hn' (by decide)
        . omega
        . apply Nat.not_prime_mul' (a := 5) (b := (n - 9)/5) (by omega) (by norm_num) (by omega)
        . omega
    -- for remainder 6, n = 21 + 5k
    . use 21
      norm_num
      and_intros
      . decide
      . use n - 21
        and_intros
        . apply Nat.Even.sub_odd (by omega) hn' (by decide)
        . omega
        . apply Nat.not_prime_mul' (a := 5) (b := (n - 21)/5) (by omega) (by norm_num) (by omega)
        . omega
    -- for remainder 8, n = 33 + 5k
    . use 33
      norm_num
      and_intros
      . decide
      . use n - 33
        and_intros
        . apply Nat.Even.sub_odd (by omega) hn' (by decide)
        . omega
        . apply Nat.not_prime_mul' (a := 5) (b := (n - 33)/5) (by omega) (by norm_num) (by omega)
        . omega