import Mathlib
/-Theorem: Let $X$ and $Y$ be positive natural numbers. Let $r = Y \pmod 3$ (where $r \in \{0,1,2\}$) and $k = \lfloor Y/3 \rfloor$. If $X^r$ (with $X^0$ interpreted as 1) can be expressed as the sum of four cubes of natural numbers, i.e., $X^r = x_1^3+x_2^3+x_3^3+x_4^3$ for some natural numbers $x_1, x_2, x_3, x_4$, then $X^Y$ can also be expressed as the sum of four cubes of natural numbers. Specifically, $X^Y = (x_1 X^k)^3 + (x_2 X^k)^3 + (x_3 X^k)^3 + (x_4 X^k)^3$.-/
theorem number_theory_642136 {X Y : ℕ} (hX : 0 < X) (hY : 0 < Y)
    (r : ℕ) (hr : r = Y % 3) (k : ℕ) (hk : k = Y / 3)
    (x : Fin 4 → ℕ) (h : ∑ i, (x i)^3 = X ^ r) :
    ∃ (x' : Fin 4 → ℕ), ∑ i, (x' i)^3 = X ^ Y := by 
  use fun i => (x i) * (X ^ k)
  have h1 : X ^ Y = X ^ r * (X ^ k) ^ 3 := by
    have hY_eq : Y = 3 * k + r := by 
      rw [hk, hr]
      omega 
    rw [hY_eq]
    ring_nf 
  have h2 : ∑ i, ((x i) * (X ^ k))^3 = (∑ i, (x i)^3) * (X ^ k) ^ 3 := by
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_mul, mul_pow, Finset.sum_range_succ]
    <;> ring 
  rw [h2, h, h1]
  <;> omega