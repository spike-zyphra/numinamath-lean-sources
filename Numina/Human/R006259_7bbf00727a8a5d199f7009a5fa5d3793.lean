import Mathlib

/- Let $K_0$ be an integer satisfying $1 \le K_0 \le 50$. A PIN is a four-digit natural number $n$. Let $x$ be the number formed by the first two digits of $n$ and $y$ be the number formed by the last two digits of $n$, so $n=100x+y$. The PIN $n$ must satisfy:
1. $n > 2021$.
2. $n$ is divisible by 5.
3. $n$ is divisible by 6.
4. The number $100y+x$ (obtained by swapping the two-digit block $x$ with the two-digit block $y$) is equal to $n + 99 K_0$.

If $K_0 = 10$, determine all possible values for $n$. Show that these values are 4050 and 7080. -/
theorem number_theory_635223 (K₀ : ℕ) (hK₀ : 1 ≤ K₀ ∧ K₀ ≤ 50) (hK₀' : K₀ = 10) :
    {n ∈ Finset.Icc 1000 9999 |
    let x := n / 100; let y := n % 100;
    n > 2021 ∧ 5 ∣ n ∧ 6 ∣ n ∧ 100 * y + x = n + 99 * K₀} = {4050, 7080} := by
  -- We plug in K₀ = 10.
  subst K₀
  -- We check all possible values of n.
  native_decide