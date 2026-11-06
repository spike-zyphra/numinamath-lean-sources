import Mathlib

/- $5 \cdot 7$ Fibonacci numbers are defined as
$$
a_{0}=0, a_{1}=a_{2}=1, a_{n+1}=a_{n}+a_{n-1}(n \geqslant 1) .
$$

Find the greatest common divisor of the 1960th and 1988th terms.
(29th International Mathematical Olympiad Shortlist, 1988) -/
theorem number_theory_160123 :
    (Nat.fib 1960).gcd (Nat.fib 1988) = 317811 := by 
  norm_num [← Nat.fib_gcd]