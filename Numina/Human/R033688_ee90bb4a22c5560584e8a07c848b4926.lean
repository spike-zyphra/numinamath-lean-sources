import Mathlib

/- Determine the minimal prime number $p>3$ for which no natural number $n$ satisfies

$$
2^{n}+3^{n} \equiv 0(\bmod p)
$$ -/
theorem number_theory_605021: IsLeast {p : ℕ | Nat.Prime p ∧ p > 3 ∧ ¬∃ n : ℕ, (2^n + 3^n) % p = 0} 19 := by
  constructor
  -- show 19 is in the set
  . simp
    norm_num
    intro n
    have h1: 2 ^ 18 % 19 = 1 := by norm_num
    have h2: 3 ^ 18 % 19 = 1 := by norm_num
    set q:= n / 18 with hq
    set r:= n % 18 with hr
    have h3: n = 18 * q + r := by omega
    rw [h3]
    by_contra! l
    have eq: (2 ^ (18 * q + r) + 3 ^ (18 * q + r)) % 19 = (2 ^ (18 * q + r) % 19 + 3 ^ (18 * q + r) % 19) % 19 := by
      rw [Nat.add_mod]
    rw [eq] at l
    clear eq
    have eq1: 2 ^ (18 * q + r) % 19 = 2 ^ r % 19 := by
      rw [show 2 ^ (18 * q + r) = (2 ^ 18) ^ q * 2 ^ r by rw [Nat.pow_add]; rw [Nat.pow_mul]]
      rw [← Nat.mod_mul_mod]
      nth_rewrite 1 [Nat.pow_mod]
      simp [h1]
    have eq2: 3 ^ (18 * q + r) % 19 = 3 ^ r % 19 := by
      rw [show 3 ^ (18 * q + r) = (3 ^ 18) ^ q * 3 ^ r by rw [Nat.pow_add]; rw [Nat.pow_mul]]
      rw [← Nat.mod_mul_mod]
      nth_rewrite 1 [Nat.pow_mod]
      simp [h2]
    simp [eq1,eq2] at l
    clear eq1 eq2 h1 h2 hq hr
    have r1: 0 ≤ r := by omega
    have r2: r ≤ 17 := by omega
    clear_value r
    interval_cases r  -- enumerate all cases for r = n % 18
    all_goals omega

  -- show 19 is the least element
  . intro p
    simp
    intro hP
    intro hp
    intro h
    by_contra! l
    absurd h
    simp
    interval_cases p -- check all cases for p
    . absurd hP
      norm_num
    . use 1
      norm_num
    . absurd hP
      norm_num
    . use 3
      norm_num
    . absurd hP
      norm_num
    . absurd hP
      norm_num
    . absurd hP
      norm_num
    . use 5
      norm_num
    . absurd hP
      norm_num
    . use 2
      norm_num
    . absurd hP
      norm_num
    . absurd hP
      norm_num
    . absurd hP
      norm_num
    . use 8
      norm_num
    . absurd hP
      norm_num
