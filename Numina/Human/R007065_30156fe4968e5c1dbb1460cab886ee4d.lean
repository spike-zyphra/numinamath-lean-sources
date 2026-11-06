import Mathlib
/-Planets X, Y and Z take 360, 450 and 540 days, respectively, to rotate around the same sun. If the three planets are lined up in a ray having the sun as its endpoint, what is the minimum positive number of days before they are all in the exact same locations again?-/
theorem algebra_21939 : lcm (lcm 360 450) 540 = 5400 := by
--We are asked to find the least common multiple of 360, 450 and 540.  We prime factorize \begin{align*}
--360 &= 2^3\cdot 3^2\cdot 5 \\
--450 &= 2 \cdot3^2 \cdot 5^2 \\
--540 &= 2^2\cdot 3^3 \cdot 5
--\end{align*} and take the largest exponent for each of the primes to get a least common multiple of $2^3\cdot 3^3\cdot 5^2=\boxed{5400}$.
  have heq : lcm 360 450 = 1800 := by
    congr
  rw [heq]
  congr
