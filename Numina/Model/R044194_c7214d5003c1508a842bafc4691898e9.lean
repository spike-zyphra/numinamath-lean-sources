import Mathlib

-- https://app.projectnumina.ai/problems/c7214d50-03c1-508a-842b-afc4691898e9
theorem algebra_605188 : {x : Fin 2017 → ℝ | ∀ i, x i * (x i - 1) = x (i + 1) - 1} = {λ _ ↦ 1} := by
  ext x
  simp
  constructor
  . intro hx
    have hx' : ∀ (i : Fin 2017), x i * (x i - 1) + 1 = x (i + 1) := by
      intro i
      rw [hx i, sub_add_cancel]
    -- we have $x_{i} \leq x_{i+1}$, notice that add for `Fin 2017` is modulo 2017, so $x_0 ≤ x_1 ≤ \cdots ≤ x_2016 ≤ x_0$,
    -- that means $x_i = x_0$ for all $i$
    have h1 (i: Fin 2017): x i ≤ x (i + 1) := by
      rw [<-hx' i]
      apply le_of_sub_nonneg
      rw [show x i * (x i - 1) + 1 - x i = (x i - 1) ^ 2 by ring_nf]
      exact sq_nonneg _
    -- $x_i ≤ x_{i+k}$ for all $i, k\in \mathbb N$
    have h2 (i: Fin 2017) (k: ℕ): x i ≤ x (i + k) := by
      induction k with
      | zero => simp
      | succ k' ih =>
        apply le_trans ih
        apply le_trans (h1 _)
        apply le_of_eq
        congr 1
        rw [<-Fin.val_eq_val, Fin.add_def, Fin.add_def, Fin.add_def]
        simp
        rw [Fin.add_def]
        simp
        ring_nf
    -- prove that $x_i \le x_0$ by setting $k = 2017 * 2 - i$ in `h1`
    have h3 (i: Fin 2017): x i ≤ x 0 := by
      let j := 2017 * 2 - i.val
      have hi_add_j : i + j = 0 := by
        rw [<-Fin.val_eq_val, Fin.add_def]
        simp [j]
        rw [Nat.add_comm, Nat.sub_add_cancel (by linarith only [i.isLt])]
      specialize h2 i j
      rw [hi_add_j] at h2
      exact h2
    -- prove that $x_i \ge x_0$ by setting $i = 0 \and k = i.val$ in `h1`
    have h4 (i: Fin 2017): x 0 ≤ x i := by
      specialize h2 0 i.val
      simp at h2
      exact h2
    -- so $x_i = x_0$ for all $i$
    have h5 (i: Fin 2017): x i = x 0 := le_antisymm (h3 i) (h4 i)
    -- each equation about $x_i$ would like to simplify to $x_0 = 1$.
    have eq1 := hx 0
    simp [show x 1 = x 0 by linarith [h5 1], show x 0 = x 0 by rfl] at eq1
    -- solve quadratic equation to get double root $x_0 = 1$
    have hx0 : x 0 = 1 := by
      nlinarith
    funext i
    linarith [h5 i, hx0]
  . -- Show that the function $x_i = 1$ for all $i$ is a solution
    intro hx
    intro i
    simp [hx]
    <;> ring_nf
    <;> norm_num