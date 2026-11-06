import Mathlib

open Finset Real

/- Five. (20 points)
Let $a_{1} \in \mathbf{R}^{+}(i=1,2, \cdots n)$. Prove: $\frac{1}{a_{1}}+\frac{2}{a_{1}+a_{2}}+\cdots+\frac{n}{a_{1}+a_{2}+\cdots+a_{n}}<$ $2 \sum_{i=1}^{n} \frac{1}{a_{i}}$. -/
theorem inequalities_223970 {n : ℕ} (hn : 0 < n) (a : ℕ → ℝ)
    (ha : ∀ i ∈ Icc 1 n, 0 < a i) :
    ∑ i ∈ Icc 1 n, (i : ℝ) / (∑ j ∈ Icc 1 i, a j) < 2 * ∑ i ∈ Icc 1 n, 1 / a i := by
  simp at ha
  -- we first need a lemma to bound the sum
  have h1: ∀k, 0<k → k ≤ n → k^2*(k+1)^2/4 ≤ (∑i∈ Icc 1 k, i^2/(a i)) * (∑i∈ Icc 1 k, a i) := by
    intro k hk1 hk2
    calc (k:ℝ) ^ 2 * (k + 1) ^ 2 / 4
    _ = (∑ i∈ Icc 1 k, i:ℝ)^2 := by
      suffices ∑ i ∈ Icc 1 k, (i:ℝ) = (k:ℝ) * (k + 1) / 2 by
        rw [this]
        ring_nf
      have : Icc 1 k = Ico 1 (k + 1) := by
        ext a'
        simp
        intro h
        omega
      rw [this]
      induction k, hk1 using Nat.le_induction with
      | base => simp
      | succ n' hmn hn =>
        rw [Finset.sum_Ico_succ_top (by omega), hn, Nat.cast_add]
        ring_nf; omega
        ext a'; simp; intro h; omega
    _ = (∑ i∈ Icc 1 k, i/√(a i) * √(a i))^2 := by apply congr_arg (fun t =>t^2); refine Finset.sum_congr rfl ?_; intro x hk; rw [div_mul, div_self (by apply ne_of_gt; simp at hk ⊢; exact ha x hk.left (by linarith)), div_one]
    -- we use Cauchy-Schwarz
    _ ≤ (∑ i ∈ Icc 1 k, (i:ℝ) ^ 2 / a i) * (∑ i ∈ Icc 1 k, a i) := by
      have h1:=Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 k) (fun i => i/(√(a i))) (fun i => √(a i))
      suffices (∑ i ∈ Icc 1 k, (↑i / √(a i)) ^ 2) * ∑ i ∈ Icc 1 k, √(a i) ^ 2 = (∑ i ∈ Icc 1 k, ↑i ^ 2 / a i) * ∑ i ∈ Icc 1 k, a i by linarith
      have h2 : (∑ i ∈ Icc 1 k, (↑i / √(a i)) ^ 2) = ∑ i ∈ Icc 1 k, (↑i ^ 2 / a i : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        simp at hx
        rw [div_pow, sq_sqrt (by linarith [ha x hx.left (by linarith)])]
      have h3 : (∑ i ∈ Icc 1 k, √(a i) ^ 2) = ∑ i ∈ Icc 1 k, a i := by
        apply Finset.sum_congr rfl
        intro x hx
        simp at hx
        rw [sq_sqrt (by linarith [ha x hx.left (by linarith)])]
      rw [h2, h3]
  -- to actually use the lemma it needs a small upgrade
  have h1':∀k, 0<k → k≤n → k/(∑i∈ Icc 1 k, a i) ≤ 4 /(k*(k+1)^2) * (∑i∈ Icc 1 k, i^2/(a i)) := by
    intro k hk1 hk2
    specialize h1 k hk1 hk2
    apply (mul_le_mul_right (a:=(∑ i ∈ Icc 1 k, a i) * ((k*(k+1)^2)/4)) (by apply mul_pos; apply Finset.sum_pos; simp; intro i hi1 hi2; exact ha i hi1 (by linarith); simp; linarith; positivity;)).mp
    conv_lhs =>
      calc _
      _ = ((∑ i ∈ Icc 1 k, a i) / ∑ i ∈ Icc 1 k, a i) *(k^2 * (↑k + 1) ^ 2 / 4) := by ring_nf
      _ = k^2 * (k+1)^2/4 := by rw [div_self (by apply ne_of_gt; apply Finset.sum_pos; simp; intro i hi1 hi2; exact ha i hi1 (by linarith); simp; linarith), one_mul]
    conv_rhs =>
      calc _
      _ = (4 / 4) * (((k * (k + 1) ^ 2))/((k * (k + 1) ^ 2))) * (∑ i ∈ Icc 1 k, i ^ 2 / a i) * ∑ i ∈ Icc 1 k, a i := by ring
      _ = (∑ i ∈ Icc 1 k, ↑i ^ 2 / a i) * ∑ i ∈ Icc 1 k, a i := by rw [div_self (by norm_num), div_self (by apply ne_of_gt; positivity), one_mul, one_mul]
    exact h1
  -- now we can solve the problem
  calc ∑ i ∈ Icc 1 n, ↑i / ∑ j ∈ Icc 1 i, a j
  -- apply our lemma
  _ ≤ ∑ i ∈ Icc 1 n, (4:ℝ)/(i*(i+1)^2) * (∑j∈ Icc 1 i, j^2/(a j)) := by
    apply Finset.sum_le_sum; intro i hi; simp at hi;
    specialize h1' i (by linarith) (by linarith)
    exact h1'
  _ = ∑ i ∈ Icc 1 n, ∑ j ∈ Icc 1 i, (4:ℝ)/(i*(i+1)^2) * (j^2/(a j)) := by apply Finset.sum_congr; rfl; intro x hx; rw [Finset.mul_sum]
  _ = ∑ j ∈ Icc 1 n, ∑ i ∈ Icc j n, (4:ℝ)/(i*(i+1)^2) * (j^2/(a j)) := by apply sum_comm'; intro x y; simp; omega
  _ = 2 * ∑ j ∈ Icc 1 n, j^2/(a j) * ∑ i ∈ Icc j n, (2:ℝ)/(i*(i+1)^2) := by rw [Finset.mul_sum]; apply Finset.sum_congr (by rfl); intro x hx; rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr (by rfl); intro x2 hx2; ring_nf
  _ = 2 * ∑ j ∈ Icc 1 n, j^2/(a j) * ∑ i ∈ Icc j n, (2:ℝ)*i/(i^2*(i+1)^2) := by apply congr_arg; apply Finset.sum_congr (by rfl); intro x hx; apply congr_arg; apply Finset.sum_congr (by rfl); intro x2 hx2; rw [show (x2:ℝ)^2=x2*x2 by ring_nf, ← div_div, ← div_div, ← div_div, ← mul_div, div_self (by simp at hx hx2; apply ne_of_gt; norm_cast; linarith [hx.left, hx2.left])]; ring_nf
  _ < 2 * ∑ j ∈ Icc 1 n, j^2/(a j) * ∑ i ∈ Icc j n, ((1:ℝ)/i^2 - (1:ℝ)/(i+1)^2) := by
    gcongr 2 * ?_; apply Finset.sum_lt_sum_of_nonempty; simp; linarith; intro i hi; gcongr i^2/(a i) * ?_; apply div_pos; norm_cast; simp at hi; apply pow_pos; linarith; simp at hi; exact ha i (by linarith) (by linarith); simp at hi; apply Finset.sum_lt_sum_of_nonempty; simp; exact hi.right; intro j hj
    conv_rhs =>
      calc _
      _ = (1:ℝ) / j ^ 2 * ((j+1)^2/(j+1)^2) - 1 / (j + 1) ^ 2 * (j^2/j^2) := by rw [div_self (by positivity), div_self (by simp at hj; apply ne_of_gt; apply pow_pos; norm_cast; linarith)]; ring_nf
      _ = (j+1)^2 / (j^2*(j+1)^2) - j^2/ (j^2*(j+1)^2) := by rw [div_mul_div_comm, div_mul_div_comm, one_mul, one_mul, mul_comm (((j:ℝ) + 1) ^ 2)];
      _ = ((j+1)^2 - j^2) / (j^2*(j+1)^2) := by ring_nf
      _ = (2 * j + 1) / (j^2*(j+1)^2) := by ring_nf
    gcongr; norm_cast; simp at hj; apply mul_pos; apply pow_pos; linarith
    apply pow_pos; linarith
    linarith
  _ = 2 * ∑ j ∈ Icc 1 n, j^2/(a j) * (1/j^2-1/(n+1)^2) := by
    apply congr_arg; apply Finset.sum_congr (by rfl); intro x hx; simp at hx
    apply congr_arg
    induction n, hx.right using Nat.le_induction with
      | base => simp
      | succ n' hmn hn =>
        rw [Finset.sum_Icc_succ_top (by linarith), hn, Nat.cast_add]; ring_nf
  _ < 2 * ∑ j ∈ Icc 1 n, j^2/(a j) * (1/j^2) := by gcongr 2*?_; apply Finset.sum_lt_sum_of_nonempty (by simp; omega); intro x hx; simp at hx; gcongr; apply div_pos; apply pow_pos; simp; linarith; exact ha x (by linarith) (by linarith); simp; apply pow_pos; linarith
  _ = 2 * ∑ j ∈ Icc 1 n, 1 / a j := by apply congr_arg; apply Finset.sum_congr (by rfl); intro x hx; rw [div_mul_div_comm, mul_one, mul_comm, ← div_div, div_self (by simp at hx; apply ne_of_gt; apply pow_pos; simp; linarith)]