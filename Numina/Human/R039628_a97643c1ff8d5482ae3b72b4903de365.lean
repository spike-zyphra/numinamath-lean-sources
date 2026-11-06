import Mathlib

open Finset Real

/- Soit $0 \leqslant x_{1} \leqslant x_{2} \leqslant \cdots \leqslant x_{n} \leqslant 1$ et $0 \leqslant y_{1} \leqslant y_{2} \leqslant \cdots \leqslant y_{n} \leqslant 1$ des réels. On pose $x_{n+1}=1$.

Prouver que

$$
\sum_{i=1}^{n}\left(x_{i}-y_{i}\right)+n \sum_{i=1}^{n}\left(x_{i+1}-x_{i}\right) y_{i} \geqslant 0
$$ -/
theorem inequalities_604350 {n : ℕ} (hn : 0 < n) (x y : ℕ → ℝ)
    (hx1 : ∀ i ∈ Icc 1 n, 0 ≤ x i)
    (hx2 : ∀ i ∈ Ico 1 n, x i ≤ x (i + 1))
    (hx3 : x n ≤ 1) (hx4 : x (n + 1) = 1)
    (hy1 : ∀ i ∈ Icc 1 n, 0 ≤ y i)
    (hy2 : ∀ i ∈ Ico 1 n, y i ≤ y (i + 1))
    (hy3 : y n ≤ 1) :
    ∑ i ∈ Icc 1 n, (x i - y i) + n * ∑ i ∈ Icc 1 n, (x (i + 1) - x i) * y i ≥ 0 := by
  -- We will reason by induction on $\mathrm{n} \geqslant 1$.
  match n with
  | 0 => linarith
  | 1 =>
    -- - For $n=1$, consider two real numbers $x_{1}, y_{1} \in [0,1]$ and set $x_{2}=1$. We need to prove that $\left(x_{1}-y_{1}\right)+\left(x_{2}-x_{1}\right) y_{1} \geqslant 0$.
    simp_all
    -- Indeed, we have $\left(x_{1}-y_{1}\right)+\left(x_{2}-x_{1}\right) y_{1}=\left(x_{1}-y_{1}\right)+\left(1-x_{1}\right) y_{1}=x_{1}\left(1-y_{1}\right) \geqslant 0$, which concludes the proof.
    calc
      x 1 - y 1 + (1 - x 1) * y 1 = x 1 * (1 - y 1) := by ring
      _ ≥ 0 := by apply mul_nonneg hx1; exact sub_nonneg.mpr hy3
  | k + 2 =>
    -- Suppose that for some $n \geqslant 1$ and for all real numbers $0 \leqslant a_{1} \leqslant a_{2} \leqslant \cdots \leqslant a_{n} \leqslant 1$ and $0 \leqslant b_{1} \leqslant b_{2} \leqslant \cdots \leqslant b_{n} \leqslant 1$ with $a_{n+1}=1$, we have
    -- $$ \sum_{i=1}^{n}\left(a_{i}-b_{i}\right)+n \sum_{i=1}^{n}\left(a_{i+1}-a_{i}\right) b_{i} \geqslant 0 $$
    let x' (i : ℕ) := x (i + 1)
    have hx1' : ∀ i ∈ Icc 1 (k + 1), 0 ≤ x' i := by
      intro i hi
      simp [x']
      apply hx1 (i + 1)
      simp at hi ⊢
      exact hi.right
    have hx2' : ∀ i ∈ Ico 1 (k + 1), x' i ≤ x' (i + 1) := by
      intro i hi
      simp [x']
      apply hx2 (i + 1)
      simp at hi ⊢
      exact hi.right
    have hx3' : x' (k + 1) ≤ 1 := by
      simp [x']
      exact hx3
    have hx4' : x' (k + 2) = 1 := by simp [x']; exact hx4
    let y' (i : ℕ) := y (i + 1)
    have hy1' : ∀ i ∈ Icc 1 (k + 1), 0 ≤ y' i := by
      intro i hi
      simp [y']
      apply hy1 (i + 1)
      simp at hi ⊢
      exact hi.right
    have hy2' : ∀ i ∈ Ico 1 (k + 1), y' i ≤ y' (i + 1) := by
      intro i hi
      simp [y']
      apply hy2 (i + 1)
      simp at hi ⊢
      exact hi.right
    have hy3' : y' (k + 1) ≤ 1 := by simp [y']; exact hy3
    have ih := by apply inequalities_604350 (show k + 1 > 0 by simp) x' y' hx1' hx2' hx3' hx4' hy1' hy2' hy3'
    -- By isolating the contributions of $x_{1}$ and $y_{1}$, we have
    -- $$ \begin{aligned} & \sum_{i=1}^{n+1}\left(x_{i}-y_{i}\right)+(n+1) \sum_{i=1}^{n+1}\left(x_{i+1}-x_{i}\right) y_{i} \ &= \sum_{i=2}^{n+1}\left(x_{i}-y_{i}\right)+n \sum_{i=2}^{n+1}\left(x_{i+1}-x_{i}\right) y_{i}+x_{1}-y_{1}+\sum_{i=2}^{n+1}\left(x_{i+1}-x_{i}\right) y_{i} \ & \quad+(n+1)\left(x_{2}-x_{1}\right) y_{1} \end{aligned} $$
    have h1 : Finset.Ioc 1 (k + 2) = Finset.Icc 2 (k + 2) := by
      ext x
      simp
      intro _
      tauto
    have hsimp : ∑ i ∈ Icc 1 (k + 2), (x i - y i) + ↑(k + 2) * ∑ i ∈ Icc 1 (k + 2), (x (i + 1) - x i) * y i =
        ∑ i ∈ Icc 2 (k + 2), (x i - y i) + ↑(k + 1) * ∑ i ∈ Icc 2 (k + 2), (x (i + 1) - x i) * y i + x 1 - y 1 + ∑ i ∈ Icc 2 (k + 2), (x (i + 1) - x i) * y i + ↑(k + 2) * (x 2 - x 1) * y 1 := by
      rw [Finset.Icc_eq_cons_Ioc (by simp), Finset.sum_cons, Finset.sum_cons]
      rw [h1, mul_add, Nat.cast_add]
      norm_num
      ring
    rw [hsimp]
    -- applied to the real numbers $a_{i}=x_{i+1}$ and $b_i=y_{i+1}$
    let g (i : ℕ) := i + 1
    have hg : ∀ x ∈ Icc 1 (k + 1), ∀ y ∈ Icc 1 (k + 1), g x = g y → x = y := by simp [g]
    have himage : image g (Icc 1 (k + 1)) = Icc 2 (k + 2) := by
      ext x
      simp
      constructor
      · intro ⟨a, ha⟩
        simp [g] at ha
        rw [←ha.right]
        simp
        exact ha.left
      · intro hx
        use x - 1
        split_ands
        · calc
            1 = 2 - 1 := by simp
            _ ≤ x - 1 := by rel [hx.left]
        · simp [hx.right]
        · simp [g]
          rw [Nat.sub_add_cancel]
          linarith [hx.left]
    have ih : ∑ i ∈ Icc 2 (k + 2), (x i - y i) + ↑(k + 1) * ∑ i ∈ Icc 2 (k + 2), (x (i + 1) - x i) * y i ≥ 0 := by
      simp only [x', y'] at ih
      have : ∑ i ∈ Icc 2 (k + 2), (x i - y i) = ∑ x_1 ∈ Icc 1 (k + 1), (x (x_1 + 1) - y (x_1 + 1)) := by rw [←himage]; exact sum_image hg
      rw [this]
      have : ∑ i ∈ Icc 2 (k + 2), (x (i + 1) - x i) * y i = ∑ x_1 ∈ Icc 1 (k + 1), (x (x_1 + 1 + 1) - x (x_1 + 1)) * y (x_1 + 1) := by rw [←himage]; exact sum_image hg
      rw [this]
      exact ih
    -- prove y i ≥ y 1
    have hyi (i : ℕ) (hi : i ∈ Icc 1 (k + 2)) : y i ≥ y 1 := by
      induction i with
      | zero => simp at hi
      | succ j ih =>
        by_cases hj : j = 0
        · simp [hj]
        · simp at hi
          have hj' : j ∈ Icc 1 (k + 2) := by
            simp
            constructor
            · exact Nat.one_le_iff_ne_zero.mpr hj
            · apply le_trans hi; norm_num
          have : y j ≥ y 1 := ih hj'
          apply le_trans this
          apply hy2
          simp
          constructor
          · exact Nat.one_le_iff_ne_zero.mpr hj
          · apply lt_of_le_of_lt hi
            norm_num
    -- simplify the result
    calc
      ∑ i ∈ Icc 2 (k + 2), (x i - y i) + ↑(k + 1) * ∑ i ∈ Icc 2 (k + 2), (x (i + 1) - x i) * y i + x 1 - y 1 + ∑ i ∈ Icc 2 (k + 2), (x (i + 1) - x i) * y i + ↑(k + 2) * (x 2 - x 1) * y 1
        ≥ 0 + x 1 - y 1 + ∑ i ∈ Icc 2 (k + 2), (x (i + 1) - x i) * y i + ↑(k + 2) * (x 2 - x 1) * y 1 := by rel [ih]
      _ = x 1 - y 1 + ∑ i ∈ Icc 2 (k + 2), (x (i + 1) - x i) * y i + ↑(k + 2) * (x 2 - x 1) * y 1 := by simp
      _ ≥ x 1 - y 1 + ∑ i ∈ Icc 2 (k + 2), (x (i + 1) - x i) * y 1 + ↑(k + 2) * (x 2 - x 1) * y 1 := by
        -- show ∑ i ∈ Icc 2 (k + 2), (x (i + 1) - x i) * y i ≥ ∑ i ∈ Icc 2 (k + 2), (x (i + 1) - x i) * y 1
        simp
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left
        · apply hyi
          simp at hi ⊢
          exact ⟨by apply le_trans ?_ hi.left; norm_num, hi.right⟩
        · simp
          by_cases  hi' : i < k + 2
          · apply hx2
            simp at hi ⊢
            constructor
            · apply le_trans ?_ hi.left; norm_num
            · exact hi'
          · simp at hi hi'
            have : i = k + 2 := by apply le_antisymm hi.right hi'
            rw [this, hx4]
            exact hx3
      _ = x 1 + y 1 * (-1 + (k + 2) * (x 2 - x 1) + ∑ i ∈ Icc 2 (k + 2), (x (i + 1) - x i)) := by
        rw [Nat.cast_add, ←Finset.sum_mul]
        rw [mul_add, mul_add]
        ring
      _ = x 1 * (1 - y 1) + (k + 1) * y 1 * (x 2 - x 1) := by
        -- show ∑_{i=2}^{k+2} (x (i + 1) - x i) = x (k + 3) - x 2
        have : ∑ i ∈ Icc 2 (k + 2), (x (i + 1) - x i) = x (k + 3) - x 2 := by
          simp
          nth_rw 2 [←himage]
          rw [sum_image hg]
          simp [g]
          nth_rw 2 [Finset.Icc_eq_cons_Ioc (by simp)]
          rw [Finset.sum_cons, Finset.Icc_eq_cons_Ico (by simp), Finset.sum_cons]
          have : Ico 2 (k + 2) = Ioc 1 (k + 1) := by
            ext x; simp
            constructor <;> intro h
            · constructor
              · exact h.left
              · linarith [h.right]
            · constructor
              · linarith [h.left]
              · linarith [h.right]
          rw [this]
          norm_num
        rw [this, hx4]
        ring
      _ ≥ 0 := by
        apply add_nonneg
        · apply mul_nonneg
          · apply hx1; simp
          · simp
            apply le_trans
            · apply hyi (k + 2); simp
            · exact hy3
        · apply mul_nonneg
          · apply mul_nonneg
            · norm_cast; norm_num
            · apply hy1; simp
          · simp
            apply hx2 1
            simp
