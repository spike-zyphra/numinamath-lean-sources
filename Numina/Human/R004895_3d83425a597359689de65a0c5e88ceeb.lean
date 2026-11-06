import Mathlib

/- The real numbers $x, y, z, m, n$ are positive, such that $m+n \geq 2$. Prove that

$$
\begin{gathered}
x \sqrt{y z(x+m y)(x+n z)}+y \sqrt{x z(y+m x)(y+n z)}+z \sqrt{x y(z+m x)(z+n y)} \leq \\
\frac{3(m+n)}{8}(x+y)(y+z)(z+x) .
\end{gathered}
$$ -/
theorem inequalities_604479 (x y z m n : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hm : 0 < m) (hn : 0 < n) (hmn : m + n ≥ 2) :
    x * Real.sqrt (y * z * (x + m * y) * (x + n * z)) +
    y * Real.sqrt (x * z * (y + m * x) * (y + n * z)) +
    z * Real.sqrt (x * y * (z + m * x) * (z + n * y)) ≤
    3 * (m + n) / 8 * (x + y) * (y + z) * (z + x) := by
  -- each item in the left hand side is less than or equal to item like $x * ((x * y + x * z + (m + n) * y * z) / 2)$
  -- this step uses AM-GM to remove the square root
  have h1 {x y z: ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z):
    x * √(y * z * (x + m * y) * (x + n * z)) ≤ x * ((x * y + x * z + (m + n) * y * z) / 2) := by
    rw [mul_le_mul_iff_of_pos_left hx]
    rw [show y * z * (x + m * y) * (x + n * z) = (x * z + m * y * z) * (x * y + n * y * z) by ring]
    have := two_mul_le_add_sq √(x * z + m * y * z) √(x * y + n * y * z)
    rw [Real.sq_sqrt, Real.sq_sqrt, mul_assoc, <-Real.sqrt_mul] at this
    linear_combination this / 2
    all_goals
      apply le_of_lt
      apply add_pos
      apply mul_pos
      assumption
      assumption
      apply mul_pos
      apply mul_pos
      assumption
      assumption
      assumption
  apply le_trans (add_le_add (add_le_add (h1 hx hy hz) (h1 hy hx hz)) (h1 hz hx hy))

  let A := x * x * y + x * x * z + x * y * y + y * y * z + x * z * z + y * z * z
  let B := x * y * z

  -- transform the inequality to a form using A and B
  rw [show
    x * ((x * y + x * z + (m + n) * y * z) / 2) +
    y * ((y * x + y * z + (m + n) * x * z) / 2) +
    z * ((z * x + z * y + (m + n) * x * y) / 2) =
    (A + 3 * (m + n) * B) / 2 by simp [A, B]; ring,
    show 3 * (m + n) / 8 * (x + y) * (y + z) * (z + x) = 3 * (m + n) / 8 * (A + 2 * B) by simp [A, B]; ring
  ]
  -- transform the inequality to $(m + n) * (6 * B) ≤ (3 * (m + n) - 4) * A$
  have (h: (m + n) * (6 * B) ≤ (3 * (m + n) - 4) * A): (A + 3 * (m + n) * B) / 2 ≤ 3 * (m + n) / 8 * (A + 2 * B) := by
    linear_combination (1/8) * h
  apply this
  -- we will prove $m + n ≤ 3 * (m + n) - 4$ and $6 * B ≤ A$
  apply mul_le_mul
  linarith only [hmn]
  on_goal 2 =>
    simp [B]
    exact le_of_lt (mul_pos (mul_pos hx hy) hz)
  on_goal 2 =>
    simp
    linarith only [hmn]
  simp only [A, B]
  -- using AM-GM to prove $6 * B ≤ A$
  let l : List ℝ := [x * x * y, x * x * z , x * y * y , y * y * z , x * z * z , y * z * z]
  let z' : Fin 6 → ℝ := λ i => List.get l i
  let w : Fin 6 → ℝ := λ i => 1
  have hw : ∀ i ∈ Finset.univ, 0 ≤ w i := by
    intro i _
    simp [w]
  have hw' : 0 < ∑ i ∈ Finset.univ, w i := by simp [w]
  have hz' : ∀ i ∈ Finset.univ, 0 ≤ z' i := by
    intro i _
    have : List.all l (λ x => 0 ≤ x) = true := by
      simp [l]
      repeat symm; constructor
      all_goals
        apply le_of_lt
        apply mul_pos
        apply mul_pos
        assumption
        assumption
        assumption
    rw [List.all_eq] at this
    simp at this
    specialize this (l.get i)
    simp at this
    exact this
  have := Real.geom_mean_le_arith_mean Finset.univ w z' hw hw' hz'
  simp [w, z', l, Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.prod_empty, Finset.sum_empty,
    Finset.univ_eq_empty, Fin.cons_succ, Fin.cons_zero] at this
  ring_nf at this
  conv at this =>
    lhs
    rw [<-mul_pow, <-mul_pow, <-Real.rpow_natCast, <-Real.rpow_mul]
    simp
    rfl
    apply le_of_lt
    exact mul_pos (mul_pos hx hy) hz
  linear_combination this * 6
