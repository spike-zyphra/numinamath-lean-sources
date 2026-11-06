import Mathlib

open Finset


/-Suppose $n$ is a [positive integer](https://artofproblemsolving.com/wiki/index.php/Positive_integer) and $d$ is a single [digit](https://artofproblemsolving.com/wiki/index.php/Digit) in [base 10](https://artofproblemsolving.com/wiki/index.php/Base_10). Find $n$ if

$\frac{n}{810}=0.d25d25d25\ldots$-/
theorem algebra_700 (d: ℕ) (h: d < 10) (n: ℕ)
  (p: HasSum (fun (i:ℕ) => (↑d * 100 + 25 : ℚ) * 10^(-(3: ℤ) * (i + 1))) (n/810)) : n = 750 := by

    /- Repeating decimals represent [rational numbers](https://artofproblemsolving.com/wiki/index.php/Rational_number).  To figure out which rational number, we sum an [infinite](https://artofproblemsolving.com/wiki/index.php/Infinite) [geometric series](https://artofproblemsolving.com/wiki/index.php/Geometric_series), $0.d25d25d25\ldots = \sum_{n = 1}^\infty \frac{d25}{1000^n} = \frac{100d + 25}{999}$. -/
    have r : HasSum (fun (i:ℕ) => (↑d * 100 + 25 : ℚ) * (10^(-(3: ℤ) * (i + 1)))) ((↑d * 100 + 25 : ℚ) / 999) := by
      apply HasSum.mul_left
      conv in 10 ^ (-3 * (↑i + 1)) =>
        tactic =>
          rw [zpow_mul, zpow_add₀, zpow_natCast, zpow_one]
          norm_num
      conv in Rat.inv 999 =>
        tactic =>
          rw [<- mul_one (Rat.inv 999), <- inv_mul_cancel₀ (a := (10^(-3: ℤ) : ℚ)), <- mul_assoc]
          norm_num

      apply HasSum.mul_right
      norm_num

      -- Rewrite the result of the sum so that it is the result of a geometric series.
      have s : ((1 - (1/1000))⁻¹: ℚ) = 1000 / 999 := by norm_num
      rw [mul_comm, <- Rat.div_def, <- s]
      apply hasSum_geometric_of_norm_lt_one (K := ℚ)
      simp [norm,abs]
      norm_num

    /- Thus $\frac{n}{810} = \frac{100d + 25}{999}$ -/
    have q := HasSum.unique p r

    /- so $n = 30\frac{100d + 25}{37} =750\frac{4d + 1}{37}$ -/
    apply_fun (· * 810) at q
    simp at q
    have q': (n: ℚ) = (↑↑d * 4 + 1) * 750 / 37 := calc
      (n :ℚ) = (↑↑d * 100 + 25) / 999 * 810 := q
      _ = (↑↑d * 100 + 25) * 30 / 37 := by ring
      _ = (↑↑d * 4 + 1) * 750 / 37 := by ring

    -- Can also use `congr`
    apply_fun (· * 37) at q'
    simp at q'

    norm_cast at q'

    /- Since 750 and 37 are [relatively prime](https://artofproblemsolving.com/wiki/index.php/Relatively_prime), $4d + 1$ must be [divisible](https://artofproblemsolving.com/wiki/index.php/Divisible) by 37, -/
    rw [mul_comm] at q'
    have q'' : 37 ∣ (↑↑d * 4 + 1) * 750 := Dvd.intro n q'
    have r : 37 ∣ (↑↑d * 4 + 1) := Nat.Coprime.dvd_of_dvd_mul_right (by norm_num) q''

    -- and the only digit for which this is possible is $d = 9$.
    interval_cases d <;> norm_num at r

    -- Thus $4d + 1 = 37$ and $n = \boxed{750}$
    norm_num at q'
    apply_fun (· / 37) at q'
    norm_num at q'
    exact q'