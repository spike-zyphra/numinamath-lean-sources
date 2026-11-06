import Mathlib

open Real

/- Montrer que

$$
\frac{a^{n}}{1+a+\ldots+a^{2 n}}<\frac{1}{2 n}
$$ -/
/- Soit a un réel strictement positif et $\mathrm{n} \geqslant 1$ un entier. Montrer que

$$
\frac{a^{n}}{1+a+\ldots+a^{2 n}}<\frac{1}{2 n}
$$ -/
theorem inequalities_607407 (a : ℝ) (ha : 0 < a) (n : ℕ) (hn : 1 ≤ n) :
    a ^ n / (∑ i ∈ Finset.Icc 0 (2 * n), a ^ i) < 1 / (2 * n) := by
  -- Puisque la difficulté réside dans le dénominateur du membre de droite, et pour plus de confort, on peut chercher à montrer la relation inverse, à savoir :
  -- $$ \frac{1+a+\ldots+a^{2 n}}{a^{n}} & gt;2 n $$
  suffices h : ∑ i ∈ Finset.Icc 0 (2 * n), a ^ i > 2 * n * a ^ n
  · calc
      _ < a ^ n / (2 * n * a ^ n) := by rel [h]
      _ = 1 / (2 * n) := by 
        rw [div_mul_cancel_right₀]
        · ring
        · apply ne_of_gt
          apply pow_pos ha
  · --  Voyons plutôt : pour $0 \leqslant i \leqslant 2 n$, on a $a^{i}+a^{2 n-i} \geqslant 2 \sqrt{a^{i} a^{2 n-i}}=$ $2 a^{n}$. 
    have hag (i : ℕ) (hi : i ∈ Finset.Icc 0 (2 * n)) : a ^ i + a ^ (2 * n - i) ≥ 2 * a ^ n := by
      simp at hi
      have {k : ℕ} : a ^ k ≥ 0 := by
        apply pow_nonneg
        exact le_of_lt ha
      apply le_of_sub_nonneg
      calc
        _ ≤ (√ (a ^ i) - √ (a ^ (2 * n - i))) ^ 2 := by apply sq_nonneg
        _ = a ^ i + a ^ (2 * n - i) - 2 * a ^ n := by
          rw [sub_sq, sq_sqrt this, sq_sqrt this, mul_assoc, ←sqrt_mul this, ←pow_add, Nat.add_sub_cancel' hi]
          rw [add_sub_right_comm]
          congr
          apply sqrt_eq_cases.mpr
          apply Or.inl
          constructor
          · ring
          · exact this
    -- Ainsi :
    -- $$ \begin{aligned} \frac{1+a+\ldots+a^{2 n}}{a^{n}} & =\frac{\left(1+a^{2 n}\right)+\left(a+a^{2 n-1}\right)+\ldots+\left(a^{n-1}+a^{n+1}\right)+a^{n}}{a^{n}} \ & \geqslant \frac{\overbrace{2 a^{n}+2 a^{n}+\ldots+2 a^{n}}^{n \text { termes }}+a^{n}}{a^{n}} \ & =\frac{(2 n+1) a^{n}}{a^{n}} \ & =2 n+1 \ & &gt;2 n \end{aligned} $$
    -- ce qui fournit l'inégalité voulue.
    calc
      _ = ∑ i ∈ Finset.range n, (a ^ i + a ^ (2 * n - i)) + a ^ n := by
        rw [Finset.sum_add_distrib]
        have h1 : ∑ i ∈ Finset.range n, a ^ (2 * n - i) = ∑ i ∈ Finset.Icc (n + 1) (2 * n), a ^ i := by
          let f (i : ℕ) := 2 * n - i
          have himg : (Finset.range n).image f = Finset.Icc (n + 1) (2 * n) := by
            ext i
            simp [f]
            constructor <;> intro h
            · obtain ⟨a, ⟨ha1, ha2⟩⟩ := h
              rw [←ha2]
              constructor
              · have : a ≤ n - 1 := by
                  exact (Nat.le_sub_one_iff_lt hn).mpr ha1
                calc
                  _ = 2 * n - (n - 1) := by
                    rw [tsub_tsub_eq_add_tsub_of_le hn]
                    nth_rw 2 [add_comm]
                    rw [show 2 = 1 + 1 by simp, add_mul, one_mul, Nat.add_sub_assoc, Nat.add_sub_cancel, add_comm]
                    simp
                  _ ≤ 2 * n - a := by rel [this]
              · simp
            · use 2 * n - i
              constructor
              · calc
                  2 * n - i ≤ 2 * n - (n + 1) := by rel [h.1]
                  _ = 2 * n - n - 1 := by rw [Nat.sub_add_eq]
                  _ = n - 1 := by 
                    congr
                    refine Eq.symm (Nat.eq_sub_of_add_eq ?_)
                    ring
                  _ < n := by exact Nat.sub_one_lt_of_lt hn
              · rw [tsub_tsub_eq_add_tsub_of_le h.2]
                rw [Nat.add_sub_cancel_left]
          rw [←himg]
          rw [Finset.sum_image]
          intro x hx y hy hxy
          simp [f] at hxy
          simp at hx hy
          apply tsub_right_inj (by linarith) (by linarith) |>.mp at hxy
          exact hxy
        -- [0 , 2n] = [0, n - 1] ∪ [n] ∪ [n + 1, n]
        have h2 : Finset.Icc 0 (2 * n) = Finset.range n ∪ Finset.Icc (n + 1) (2 * n) ∪ {n} := by
          ext x
          simp
          constructor <;> intro h
          · simp [h]
            by_cases h' : x = n
            · simp [h']
            · rcases lt_or_gt_of_ne h' with h' | h'
              · simp [h']
              · have : x ≥ n + 1 := by exact h'
                simp [this]
          · rcases h with h | h | h
            all_goals linarith [h]
        -- [0, n - 1]  [n]  [n + 1, n] are pairwise disjoint
        have h3 : Disjoint (Finset.range n ∪ Finset.Icc (n + 1) (2 * n)) {n} := by simp
        have h4 : Disjoint (Finset.range n) (Finset.Icc (n + 1) (2 * n)) := by
          intro x hx1 hx2 i hi
          have : i < n := by
            apply hx1 at hi
            simp at hi
            exact hi
          have : ¬ i < n := by
            apply hx2 at hi
            simp at hi
            linarith
          contradiction
        -- rewrite the sum
        rw [h1, h2, Finset.sum_union h3, Finset.sum_union h4]
        simp
      _ ≥ ∑ i ∈ Finset.range n, (2 * a ^ n) + a ^ n := by
        -- apply the AM-GM inequality
        simp only [add_le_add_iff_right]
        apply Finset.sum_le_sum
        intro i hi
        apply hag
        simp at hi ⊢
        linarith
      _ > _ := by
        simp
        ring_nf
        simp
        apply pow_pos ha
    
