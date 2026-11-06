import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals

/-- A [sequence](https://artofproblemsolving.com/wiki/index.php/Sequence) of numbers $x_{1},x_{2},x_{3},\ldots,x_{100}$ has the property that, for every [integer](https://artofproblemsolving.com/wiki/index.php/Integer) $k$ between $1$ and $100,$ inclusive, the number $x_{k}$ is $k$ less than the sum of the other $99$ numbers. Given that $x_{50} = m/n,$ where $m$ and $n$ are relatively prime positive integers, find $m + n$. -/
theorem algebra_711 {x : Fin 100 → ℚ} (hx : ∀ k, x k = (∑ i, x i) - x k - (k + 1)) :
    (x 49).num + (x 49).den = 173 := by

  -- It is enough to find $x_50$ and sum the numerator and denominator.
  suffices x 49 = (75 : ℤ) / (98 : ℤ) from ?_
  · rw [this,
        Rat.num_div_eq_of_coprime (by trivial) (by decide),
        Rat.den_div_eq_of_coprime (by trivial) (by decide)]
    rfl

  -- Let the sum of all of the terms in the sequence be $\mathbb{S}$
  · set S := ∑ i, x i with hS

    -- Each term is given in terms of the sum.
    replace hx (k : Fin 100): 2 * (x k) = S - 1 - k := by
      rw [two_mul]
      nth_rewrite 1 [hx k]
      ring

    have hx49 := hx 49
    have : (((49 : Fin 100) : ℕ) : ℚ) = (49 : ℚ) := by decide
    rw [this] at hx49

    -- Therefore, it is enough to find $S$.
    suffices S = 2525/49 from by nlinarith

    /- Summing the relation up for all $k$ from $1, 2, \ldots, 100$ and solve for $S$. -/
    have hS : 2 * S = 100 * S - 5050 := by
      calc 2 * S = 2 * ∑ i, x i := by rfl
              _ = ∑ i, 2 * x i := by rw [←Finset.mul_sum]
              _ = ∑ i : Fin 100, (S - 1 - i) := by simp_rw [hx]
              _ = (∑ i : Fin 100, (S - 1)) - ∑ i : Fin 100, (i : ℚ) := by rw [Finset.sum_sub_distrib]
              _ = 100 * (S - 1) - ∑ i : Fin 100, (i : ℚ) := by rw [Finset.sum_const]; simp
              _ = 100 * (S - 1) - 99 * 50 := by congr
                                                rw [Fin.sum_univ_eq_sum_range, ←Nat.cast_sum]
                                                norm_cast
              _ = 100 * S - 5050 := by linarith

    nlinarith