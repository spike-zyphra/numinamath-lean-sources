import Mathlib

/- A plane $P$ is parmeterized by
\[\mathbf{v} = \begin{pmatrix} 1 \\ 6 \\ 7 \end{pmatrix} + t \begin{pmatrix} 2 \\ -1 \\ -1 \end{pmatrix} + s \begin{pmatrix} 2 \\ -3 \\ -5 \end{pmatrix},\]and line $L$ is parameterized by
\[\mathbf{w} = \begin{pmatrix} 7 \\ 4 \\ 1 \end{pmatrix} + u \begin{pmatrix} 3 \\ 0 \\ -1 \end{pmatrix}.\]Find the intersection of plane $P$ and line $L.$ -/
theorem calculus_21984 (P L : Set (Fin 3 → ℝ))
    (hP : P = {v | ∃ t s : ℝ, v = ![1, 6, 7] + s • ![2, -1, -1] + t • ![2, -3, -5]})
    (hL : L = {w | ∃ u : ℝ, w = ![7, 4, 1] + u • ![3, 0, -1]}) :
    P ∩ L = {![1, 4, 3]} := by
  ext x
  constructor
  · -- if $x$ is the intersection of $P$ and $L$, then $x = \begin{pmatrix} 1 \\ 4 \\ 3 \end{pmatrix}$
    intro xin
    rw [hP, hL] at xin
    rcases xin.1 with ⟨s, t, hxP⟩
    rcases xin.2 with ⟨u, hxL⟩
    rw [hxP] at hxL
    have eq1 := congrFun hxL 0
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.smul_cons, smul_eq_mul, mul_neg, mul_one, Matrix.smul_empty, Matrix.add_cons, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_add_empty, Fin.isValue, Pi.add_apply, Matrix.cons_val_zero, mul_zero] at eq1
    have eq2 := congrFun hxL 1
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.smul_cons, smul_eq_mul, mul_neg, mul_one, Matrix.smul_empty, Matrix.add_cons, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_add_empty, Fin.isValue, Pi.add_apply, Matrix.cons_val_one, mul_zero, add_zero] at eq2
    have eq3 := congrFun hxL 2
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.smul_cons, smul_eq_mul, mul_neg, mul_one, Matrix.smul_empty, Matrix.add_cons, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_add_empty, Fin.isValue, Pi.add_apply, Matrix.cons_val_two, mul_zero] at eq3
    ext i
    fin_cases i
    any_goals
    simp [hxP]
    linarith
  · -- if $x = \begin{pmatrix} 1 \\ 4 \\ 3 \end{pmatrix}$ then $x$ is the intersection of $P$ and $L$
    intro xeq
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Set.mem_singleton_iff] at xeq
    constructor
    -- $x \in P$
    rw [hP, xeq]
    use 1
    use -1
    norm_num
    -- $x \in L$
    rw [hL, xeq]
    use -2
    norm_num