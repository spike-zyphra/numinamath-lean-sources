import Mathlib

/- Let $a_{1}, a_{2}, \ldots, a_{n}, b_{1}, b_{2}, \ldots, b_{n}$ be positive real numbers such that $a_{1}+a_{2}+\cdots+a_{n}=b_{1}+b_{2}+$ $\cdots+b_{n}$. Show that

$$
\frac{a_{1}^{2}}{a_{1}+b_{1}}+\frac{a_{2}^{2}}{a_{2}+b_{2}}+\cdots+\frac{a_{n}^{2}}{a_{n}+b_{n}} \geq \frac{a_{1}+a_{2}+\cdots+a_{n}}{2}
$$ -/
theorem inequalities_604382 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hsum : ∑ i, a i = ∑ i, b i) :
    ∑ i, (a i)^2 / (a i + b i) ≥ (∑ i, a i) / 2 := by
    -- by Cauchy-schwarz inequality (or Titu's lemma), following holds.
    have h1: ∑ i, (a i)^2 / (a i + b i) ≥
      (∑i, a i)^2 / (∑ i, (a i + b i)) := by
      apply Finset.sq_sum_div_le_sum_sq_div _ _ (fun i _ => ?_)
      apply add_pos (ha i) (hb i)
    -- since sum ai = sum bi, sum (ai + bi) = 2 (sum ai)
    have h2: ∑ i, (a i + b i) = 2 * (∑ i, a i) := by
      rw [Finset.sum_add_distrib, ← hsum, two_mul]
    -- so (sum ai)^2 / (sum ai+bi) = (sum ai)^2 / 2(sum ai) = (sum ai)/2
    have h3: (∑ i, a i)^2 / (∑ i, (a i + b i)) = (∑ i, a i) / 2 := by
      rw [h2, pow_two]
      have: 0 < ∑ i, a i := by
        apply Finset.sum_pos
        · simp [ha]
        · rwa [Finset.univ_nonempty_iff, ← Fin.pos_iff_nonempty]
      field_simp [this.ne']
      ring
    -- done.
    rwa [← h3]