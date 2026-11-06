import Mathlib

/- Show that the Möbius function defined by
$$\mu(n)=\left\{\begin{array}{ll}
1 & \text { if } n=1 \\
(-1)^{s} & \text { if } n \text { is square-free with prime factorization } \\
\quad n=p_{1} p_{2} \cdots p_{s} \\
0 & \text { if } n \text { has a square factor larger than } 1
\end{array}\right.$$
is multiplicative.-/
theorem number_theory_4880(n m : ℕ) (hcop : n.Coprime m) :
    (ArithmeticFunction.moebius n) * (ArithmeticFunction.moebius m) =
    ((ArithmeticFunction.moebius (n * m))) :=
  -- directly use term proof
  Eq.symm (ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
    ArithmeticFunction.isMultiplicative_moebius hcop)
