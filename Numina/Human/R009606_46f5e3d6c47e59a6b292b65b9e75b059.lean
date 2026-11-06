import Mathlib

open Real

/- Let $n$ be a positive integer, and let $x$ and $y$ be positive real numbers such that $x^{n}+y^{n}=1$.
   Prove that  $$ \left(\sum_{k=1}^{n} \frac{1+x^{2 k}}{1+x^{4 k}}\right)\left(\sum_{k=1}^{n} \frac{1+y^{2 k}}{1+y^{4 k}}\right)<\frac{1}{(1-x)(1-y)} $$  (Estonia) -/
theorem inequalities_23627 (n : ℕ) (x y : ℝ) (hn : 0 < n) (hx : 0 < x) (hy : 0 < y)
    (h : x^n + y^n = 1) :
    (∑ k in Finset.Icc 1 n, (1 + x^(2 * k)) / (1 + x^(4 * k))) *
    (∑ k in Finset.Icc 1 n, (1 + y^(2 * k)) / (1 + y^(4 * k))) <
    1 / ((1 - x) * (1 - y)) := by
    -- For each real $t \in(0,1)$, $$ \frac{1+t^{2}}{1+t^{4}}=\frac{1}{t}-\frac{(1-t)\left(1-t^{3}\right)}{t\left(1+t^{4}\right)}&lt;\frac{1}{t} $$
    have h1 : ∀ t : ℝ, 0 < t → t < 1 → (1 + t ^ 2) / (1 + t ^ 4) < 1 / t := by
      intro t ht1 ht2
      have : (1 + t ^ 2) / (1 + t ^ 4) = 1 / t - (1 - t) * (1 - t ^ 3) / (t * (1 + t ^ 4)) := by
        field_simp ;ring
      rw [this] ;apply sub_lt_self ;field_simp ;apply mul_pos ;linarith ;simp
      refine pow_lt_one₀ (by linarith) ht2 (by simp)
    -- Substituting $t=x^{k}$ and $t=y^{k}$,
    -- $$ 0&lt;\sum_{k=1}^{n} \frac{1+x^{2 k}}{1+x^{4 k}}&lt;\sum_{k=1}^{n} \frac{1}{x^{k}}=\frac{1-x^{n}}{x^{n}(1-x)} \quad \text { and }
    -- \quad 0&lt;\sum_{k=1}^{n} \frac{1+y^{2 k}}{1+y^{4 k}}&lt;\sum_{k=1}^{n} \frac{1}{y^{k}}=\frac{1-y^{n}}{y^{n}(1-y)} $$
    have hx' : x < 1 := by
      have : x ^ (↑n : ℝ) < 1 := by rw [← h] ;simp ;exact pow_pos hy n
      refine (rpow_lt_one_iff' (by linarith) (Nat.cast_pos'.mpr hn)).mp this
    have hy' : y < 1 := by
      have : y ^ (↑n : ℝ) < 1 := by rw [← h] ;simp ;exact pow_pos hx n
      refine (rpow_lt_one_iff' (by linarith) (Nat.cast_pos'.mpr hn)).mp this
    have h2 : ∀ t:ℝ , 0 < t → t < 1 → 0 < (∑ k in Finset.Icc 1 n, (1 + t^(2 * k)) / (1 + t^(4 * k))) ∧
      (∑ k in Finset.Icc 1 n, (1 + t^(2 * k)) / (1 + t^(4 * k))) < (1 - t ^ n) / (t ^ n * (1 - t)) := by
      intro t ht1 ht2
      constructor
      · apply Finset.sum_pos
        intro i hi ;field_simp
        have : 0 < t ^ (4*i) := by exact pow_pos ht1 (4*i)
        linarith ;simp ;exact hn
      have : (1 - t ^ ((n-1) + 1)) / (t ^ ((n-1) + 1) * (1 - t)) =  ∑ k ∈ Finset.Icc 1 ((n-1) +1), 1/ t^k := by
        induction (n - 1) with
        | zero =>
          field_simp ;rw [mul_comm,div_self] ;simp ;constructor ;linarith
          refine sub_ne_zero.mpr ?_ ;exact ne_of_gt ht2
        | succ d hd =>
          have : (Finset.Icc 1 (d + 1 + 1)).erase (d+1+1) = Finset.Icc 1 (d + 1) := by
            simp ;exact rfl
          have this' : (d+1+1) ∈ (Finset.Icc 1 (d + 1 + 1)) := by simp
          rw [← Finset.sum_erase_add (Finset.Icc 1 (d + 1 + 1)) (fun i => 1 / t ^ i) this']
          rw [this,← hd]
          have h1 : (1 - t ^ (d + 1)) / (t ^ (d + 1) * (1 - t)) = t * (1 - t ^ (d + 1)) / (t ^ (d + 1 + 1) * (1 - t)) := by
            rw [pow_add t (d+1),pow_one,mul_comm (t ^ (d+1)) t,mul_assoc]
            refine Eq.symm (mul_div_mul_left (1 - t ^ (d + 1)) (t ^ (d + 1) * (1 - t)) (by linarith))
          have h2 : 1 / t ^ (d + 1 + 1) =  1 * (1-t) / (t ^ (d + 1 + 1) * (1 - t)) := by
            rw [mul_div_mul_right] ;by_contra! ;linarith
          rw [h1,h2,one_mul] ;ring
      have this' : n - 1 + 1 = n := by exact Nat.sub_add_cancel hn
      rw [this'] at this ;rw [this]
      apply Finset.sum_lt_sum_of_nonempty ;simp ;exact hn
      intro i hi ;simp at hi
      specialize h1 (t^i) (by simp [ht1]) (by refine pow_lt_one₀ (by linarith) ht2 (by linarith))
      rw [mul_comm,mul_comm 4,pow_mul,pow_mul] ;linarith
    -- Since $1-y^{n}=x^{n}$ and $1-x^{n}=y^{n}$,
    -- $$ \frac{1-x^{n}}{x^{n}(1-x)}=\frac{y^{n}}{x^{n}(1-x)}, \quad \frac{1-y^{n}}{y^{n}(1-y)}=\frac{x^{n}}{y^{n}(1-y)} $$
    -- and therefore $$ \left(\sum_{k=1}^{n} \frac{1+x^{2 k}}{1+x^{4 k}}\right)\left(\sum_{k=1}^{n} \frac{1+y^{2 k}}{1+y^{4 k}}\right)
    -- &lt;\frac{y^{n}}{x^{n}(1-x)} \cdot \frac{x^{n}}{y^{n}(1-y)}=\frac{1}{(1-x)(1-y)} . $$
    have ⟨h2x,h2x'⟩ := h2 x hx hx'
    have ⟨h2y,h2y'⟩ := h2 y hy hy'
    nth_rewrite 3 [← h] at h2x' ;simp at h2x'
    nth_rewrite 3 [← h] at h2y' ;simp at h2y'
    have h3 := mul_lt_mul_of_pos h2x' h2y' h2x (by linarith)
    have h4 : y ^ n / (x ^ n * (1 - x)) * (x ^ n / (y ^ n * (1 - y))) = 1 / ((1 - x) * (1 - y)) := by
      field_simp ;rw [mul_assoc (x^n),mul_comm (1-x),← mul_assoc,← mul_assoc,mul_assoc,mul_comm]
      nth_rewrite 1 [← mul_one (x^n * y^n)] ;rw [mul_div_mul_left] ;ring ;simp
      constructor ;intro h ;linarith ;intro y ;linarith
    rw [h4] at h3
    exact h3