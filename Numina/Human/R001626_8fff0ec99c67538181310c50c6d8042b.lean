import Mathlib

open Matrix Finset

/- If A is a (n+1)-matrix and A' is the submatrix of A obtained by removing the first line/column, x is a n-dim vector,
  then ∑ i, Aji * (a, x) = A 0 0 * a + ∑ i, A 0 (i + 1) * x i, for j = 0;
  = A j 0 * a + ∑ i, Al (j - 1) i * x i, for j > 0. -/
lemma submatrix_mul_cons {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (x : Fin n → ℝ) (a : ℝ) {j : Fin (n + 1)} :
    ∑ i, A j i * (Fin.cons a x : Fin (n + 1) → ℝ) i =
    if h : j = 0 then (A 0 0 * a + ∑ i, A 0 i.succ * x i) else (A j 0 * a + ∑ i, (A.submatrix Fin.succ Fin.succ (j.pred h) i) * x i) := by
  simp [Fin.sum_univ_succ]
  by_cases hj : j = 0
  · simp [hj]
  · simp [hj]


/- 11. (POL 3) The matrix  $$ \left(\begin{array}{ccc} a_{11} & \ldots & a_{1 n} \\ \vdots & \ldots & \vdots \\ a_{n 1} &
\ldots & a_{n n} \end{array}\right) $$  satisfies the inequality $\sum_{j=1}^{n}\left|a_{j 1} x_{1}+\cdots+a_{j n} x_{n}\right|
\leq M$ for each choice of numbers $x_{i}$ equal to $\pm 1$. Show that  $$ \left|a_{11}+a_{22}+\cdots+a_{n n}\right| \leq M $$ -/
theorem inequalities_24885 {n : ℕ} (hn : n > 0) (A : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)
    (hA : ∀ (x : Fin n → ℝ), (∀ i, x i = 1 ∨ x i = -1) → (∑ j : Fin n, |∑ i, A j i * x i| ≤ M)) :
    |A.trace| ≤ M := by
  -- prove by induction on n
  induction n, hn using Nat.le_induction generalizing M
  case base =>
    -- If n = 1, then A.trace = A 0 0
    have htrace : A.trace = A 0 0 := by
      apply Matrix.trace_fin_one
    -- By the hypothesis, we have that for x = 1, we have |A 0 0| ≤ M
    obtain hA := hA 1 (by simp)
    simp [Matrix.mulVec_one] at hA
    rw [htrace]
    exact hA
  case succ n hn ih =>
    -- If n > 1, we can remove the first row and column of A to get a submatrix A'
    let A' := A.submatrix Fin.succ Fin.succ
    -- We proved that for any x such that x i = 1 or -1, we have ∑ j, |∑ i, A' j i * x i| ≤ M - |A 0 0|
    have hA' : ∀ (x : Fin n → ℝ), (∀ i, x i = 1 ∨ x i = -1) → (∑ j : Fin n, |∑ i, A' j i * x i| ≤ M - |A 0 0|) := by
      intro x hx
      -- For any x, we can construct two vectors x₁ and x₂ of dimension n + 1, such that
      -- x₁ = (1, x) and x₂ = (-1, x).
      let x₁ : Fin (n + 1) → ℝ := Fin.cons 1 x
      let x₂ : Fin (n + 1) → ℝ := Fin.cons (-1) x
      -- We have that for any i, x₁ i = 1 or -1, and for any i, x₂ i = 1 or -1.
      have hx₁ : ∀ i, x₁ i = 1 ∨ x₁ i = -1 := by
        intro i
        rcases Fin.eq_zero_or_eq_succ i with hi | hi
        · simp [hi, x₁]
        · obtain ⟨j, hj⟩ := hi
          simp [hj, x₁]
          apply hx
      have hx₂ : ∀ i, x₂ i = 1 ∨ x₂ i = -1 := by
        intro i
        rcases Fin.eq_zero_or_eq_succ i with hi | hi
        · simp [hi, x₂]
        · obtain ⟨j, hj⟩ := hi
          simp [hj, x₂]
          apply hx
      -- Apply the hypothesis to x₁ and x₂, we obtain that
      -- ∑ j, |∑ i, A j i * x₁ i| ≤ M and ∑ j, |∑ i, A j i * x₂ i| ≤ M
      obtain h₁ := hA x₁ hx₁
      obtain h₂ := hA x₂ hx₂
      -- By our lemma, we have that
      -- |A 0 0 * a + ∑ i, A 0 (i + 1) * x i| + ∑ j > 0, |A j 0 * a + ∑ i, Al (j - 1) i * x i| ≤ M for both a = 1 and a = -1.
      simp [submatrix_mul_cons, Fin.sum_univ_succ, x₁, x₂] at h₁ h₂
      apply add_le_add h₁ at h₂
      -- Add the two inequalities, we obtain that
      -- |A 0 0 + ∑ i, A 0 (i + 1) * x i| + |-A 0 0 + ∑ i, A 0 (i + 1) * x i| + ∑ j > 0, (|A j 0 + ∑ i, Al (j - 1) i * x i| + |-A j 0 + ∑ i, Al (j - 1) i * x i|) ≤ 2M
      apply le_sub_left_of_add_le
      apply le_of_mul_le_mul_of_pos_right (a := 2)
      · ring_nf at h₂
        apply le_trans ?_ h₂
        -- Note that |A 0 0 + ∑ i, A 0 (i + 1) * x i| + |-A 0 0 + ∑ i, A 0 (i + 1) * x i| ≥ 2 * |A 0 0|
        trans |A 0 0 + ∑ x_1 : Fin n, A 0 x_1.succ * x x_1| + |-A 0 0 + ∑ x_1 : Fin n, A 0 x_1.succ * x x_1| + (∑ x_1 : Fin n, |A x_1.succ 0 + ∑ x_2 : Fin n, A x_1.succ x_2.succ * x x_2| + ∑ x_1 : Fin n, |-A x_1.succ 0 + ∑ x_2 : Fin n, A x_1.succ x_2.succ * x x_2|)
        · rw [add_mul]
          gcongr
          · trans |A 0 0 + ∑ x_1 : Fin n, A 0 x_1.succ * x x_1 - (-A 0 0 + ∑ x_1 : Fin n, A 0 x_1.succ * x x_1)|
            · ring_nf
              rw [abs_mul]
              simp
            · apply abs_sub
          · -- and |A j 0 + ∑ i, Al (j - 1) i * x i| + |-A j 0 + ∑ i, Al (j - 1) i * x i| ≥ 2 * |∑ i, Al (j - 1) i * x i|, we have
            -- 2 * |A 0 0| + 2 * ∑ j, |∑ i, Al j i * x i| ≥ 2 * M.
            rw [←Finset.sum_add_distrib, Finset.sum_mul]
            gcongr
            apply le_trans ?_ (abs_add_le _ _)
            ring_nf
            rw [abs_mul]
            simp [A']
        · apply le_of_eq
          ring
      · simp
    -- Apply the induction hypothesis to A', we obtain that |A'.trace| ≤ M - |A 0 0|
    apply ih A' at hA'
    have htrace : A.trace = A'.trace + A 0 0 := by
      simp [A']
      rw [←Matrix.trace_submatrix_succ]
      ring
    rw [htrace]
    -- Therefore, |A.trace| = |A'.trace + A 0 0| ≤ M - |A 0 0| + |A 0 0| = M
    trans |A'.trace| + |A 0 0|
    · exact abs_add_le A'.trace (A ↑0 ↑0)
    · exact le_sub_iff_add_le.mp hA'
