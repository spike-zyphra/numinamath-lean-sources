import Mathlib

/- Soyit ( $a_{n}$ ) une suite de réels. On suppose que $a_{0}=1$ et que pour tout $n \geqslant 1, a_{n}$ est la plus petite solution strictement positive de

$$
\left(a_{n}-a_{n-1}\right)\left(a_{n}+a_{n-1}-2 \sqrt{n}\right)=2 .
$$

Trouver le plus petit entier $n$ tel que $a_{n} \geqslant 2022$. -/
/- Soit ( $a_{n}$ ) une suite de réels. On suppose que $a_{0}=1$ et que pour tout $n \geqslant 1, a_{n}$ est la plus petite solution strictement positive de

$$
\left(a_{n}-a_{n-1}\right)\left(a_{n}+a_{n-1}-2 \sqrt{n}\right)=2 .
$$

Trouver le plus petit entier $n$ tel que $a_{n} \geqslant 2022$. -/
theorem algebra_607365 {a : ℕ → ℝ} (ha0 : a 0 = 1)
    (han : ∀ n ≥ 1, IsLeast {x | x > 0 ∧ (x - a (n - 1)) * (x + a (n - 1) - 2 * Real.sqrt n) = 2}
      (a n)) :
    IsLeast {n | a n ≥ 2022} (1011 ^ 2) := by

  -- We will prove that $a_n = \sqrt{n} + \sqrt{n+1}$ for all $n$ by induction.
  have han {n: ℕ}: a n = √n + √(n + 1) := by
    induction n with
    | zero => simp [ha0]
    | succ n' ih =>
      specialize han (n' + 1) (by linarith)
      -- solve the equation in the set
      -- we get $x = \sqrt{n' + 1} - \sqrt{n' + 2} \or x = \sqrt{n' + 1} + \sqrt{n' + 2}$
      conv at han =>
        arg 1
        arg 1
        intro x
        arg 2
        simp
        rw [
          ih,
          show x - (√n' + √(n' + 1)) = x - √(n' + 1) - √n' by ring,
          show x + (√n' + √(n' + 1)) - 2 * √(n' + 1) = x - √(n' + 1) + √n' by ring,
          mul_comm,
          <-sq_sub_sq,
          Real.sq_sqrt (by linarith),
          <-sub_eq_zero,
          show (x - √(n' + 1)) ^ 2 - n' - 2 = (x - √(n' + 1)) ^ 2 - (n' + 2) by ring,
          show (n' + 2) = √(n' + 2) ^ 2 by rw [Real.sq_sqrt (by linarith)],
          sq_sub_sq,
          mul_eq_zero,
          sub_add,
          sub_eq_zero,
          <-sub_add_eq_sub_sub,
          sub_eq_zero,
        ]
      -- prove that the only solution is $\sqrt{n' + 1} + \sqrt{n' + 2}$ beacuse the other one is negative
      have hset : {x | x > 0 ∧ (x = √(↑n' + 1) - √(↑n' + 2) ∨ x = √(↑n' + 1) + √(↑n' + 2))} = {√(↑n' + 1) + √(↑n' + 2)} := by
        ext x
        simp
        constructor
        . intro h
          rw [and_or_left] at h
          cases h with
          | inl h =>
            have : x < 0 := by
              rw [h.2]
              apply sub_neg_of_lt
              apply Real.sqrt_lt_sqrt
              norm_cast
              simp
              simp
            linarith
          | inr h =>
            exact h.2
        . intro h
          constructor
          . rw [h]
            apply add_pos
            rw [Real.sqrt_pos]; norm_cast; simp
            rw [Real.sqrt_pos]; norm_cast; simp
          . rw [h]
            simp
      -- Finish the proof
      rw [hset] at han
      unfold IsLeast lowerBounds at han
      simp at han
      simp
      rw [show (n':ℝ) + 1 + 1 = n' + 2 by ring]
      exact han.1
  -- prove that $1011^2$ is the smallest $n$ such that $\sqrt{n} + \sqrt{n + 1} \geq 2022$
  unfold IsLeast lowerBounds
  simp only [ge_iff_le, Set.mem_setOf_eq]
  constructor
  -- show that $\sqrt{1011^2} + \sqrt{1011^2 + 1} \geq 2022$
  . rw [han]
    rw [Nat.cast_pow, Real.sqrt_sq (by norm_num)]
    have : 1011 < √(1011 ^ 2 + 1) := by
      rw [Real.lt_sqrt (by norm_num)]
      simp
    linear_combination this
  -- show that $1011^2$ is the least number
  . intro n hn
    rw [han] at hn
    by_contra n_max
    simp only [not_le] at n_max
    have h1 : √n < 1011 := by
      rw [Real.sqrt_lt (by norm_num) (by norm_num)]
      norm_cast
    have h2 : √(↑n + 1) ≤ 1011 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_cast
    linarith only [h1, h2, hn]
