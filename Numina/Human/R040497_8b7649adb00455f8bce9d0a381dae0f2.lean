import Mathlib

open Real

/- Let $n$ be a positive integer and let $x_{1}, \ldots, x_{n}$ be real numbers. Show that

$$
\sum_{i=1}^{n} x_{i}^{2} \geqslant \frac{1}{n+1}\left(\sum_{i=1}^{n} x_{i}\right)^{2}+\frac{12\left(\sum_{i=1}^{n} i x_{i}\right)^{2}}{n(n+1)(n+2)(3 n+1)}
$$ -/
theorem inequalities_605656 (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) :
    ∑ i, (x i)^2 ≥ (1 / (n + 1)) * (∑ i, x i)^2 +
    (12 * (∑ i, (i+1) * x i)^2) / (n * (n + 1) * (n + 2) * (3 * n + 1)) := by
    -- Let $S=\frac{1}{n+1} \sum_{i=1}^{n} x_{i}$, and $y_{i}=x_{i}-S$ for $1 \leqslant i \leqslant n$.
    let S := (1 / (n + 1)) * ∑ i, x i
    let y : Fin n → ℝ := fun i => x i - S
    -- Then we have
    -- $$ \sum_{i=1}^{n} i x_{i}=\sum_{i=1}^{n} i y_{i}+\frac{n(n+1)}{2} S $$
    have h1 : ∑ i, (i+1) * x i = ∑ i, (i+1) * y i + (n * (n + 1) / 2) * S := by
      have h2 : ∑ i, (i+1) * y i = ∑ i, (i+1) * x i - S * ∑ i : Fin n, ((↑i:ℝ)+1)  := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        simp [y] ;rw [mul_sub] ;ring
      have h3 : ∑ i : Fin n, ((↑i:ℝ)+1) = (n * (n + 1) / 2) := by
        have : ∑ i : Fin n, (↑i:ℝ) = ∑ i ∈ Finset.range n, i := by
          simp ;exact Fin.sum_univ_eq_sum_range Nat.cast n
        rw [Finset.sum_add_distrib,this,Finset.sum_range_id,Finset.sum_const]
        simp ;rw [Nat.cast_div, Nat.cast_mul, Nat.cast_sub] ;ring_nf
        exact hn
        rw [← Finset.sum_range_id_mul_two n] ;exact Nat.dvd_mul_left 2 (∑ i ∈ Finset.range n, i)
        simp
      rw [h2, h3] ;ring
    -- and $$ \sum_{i=1}^{n} y_{i}^{2}=\sum_{i=1}^{n} x_{i}^{2}-2 S \sum_{i=1}^{n} x_{i}+n S^{2}=\sum_{i=1}^{n} x_{i}^{2}-\frac{1}{n+1}\left(\sum_{i=1}^{n} x_{i}\right)^{2}-S^{2} $$
    have h4 : ∑ i, y i^2 = ∑ i, x i^2 - (1 / (n + 1)) * (∑ i, x i)^2 - S^2 := by
      simp only [y]
      have h5 : ∑ i, (x i - S)^2 = ∑ i, (x i^2 - 2 * S * x i + S^2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [h5, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, ← Finset.mul_sum] ;simp
      have h6 : ∑ i, x i = (n + 1) * S := by simp [S,← mul_assoc] ;rw [mul_inv_cancel₀ (Nat.cast_add_one_ne_zero n),one_mul]
      rw [h6,pow_two ((↑n + 1)*S),← mul_assoc (((↑n:ℝ) + 1)⁻¹),← mul_assoc (((↑n:ℝ) + 1)⁻¹),
        inv_mul_cancel₀ (Nat.cast_add_one_ne_zero n),one_mul,mul_comm S,mul_assoc ((↑n:ℝ) + 1),← pow_two]
      ring
    -- Now, by the Cauchy-Schwarz inequality
    -- $$ \begin{aligned} \left(\sum_{i=1}^{n} i x_{i}\right)^{2} & =\left(\sum_{i=1}^{n} i y_{i}+\frac{n(n+1)}{2} S\right)^{2}
    -- \ & \leqslant\left(\sum_{i=1}^{n} i^{2}+\frac{n^{2}(n+1)^{2}}{4}\right)\left(\sum_{i=1}^{n} y_{i}^{2}+S^{2}\right)
    -- \ & =\frac{n(n+1)(n+2)(3 n+1)}{12} \cdot\left(\sum_{i=1}^{n} x_{i}^{2}-\frac{1}{n+1}\left(\sum_{i=1}^{n} x_{i}\right)^{2}\right) \end{aligned} $$
    -- which completes our proof.
    have h7 : (∑ i, (i+1) * x i) ^ 2 ≤ (∑ i : Fin n,((↑i:ℝ)+1)^2 + (n*(n+1)/2)^2) * (∑ i, y i^2 + S^2) := by
      rw [h1]
      let f : ℕ → ℝ := fun i => if i < n then (i+1) else (n*(n+1)/2)
      let g : ℕ → ℝ := fun i => if h : i < n then y ⟨i, h⟩ else S
      have h8 : ∑ i : Fin n, (↑↑i + 1) * y i + ↑n * (↑n + 1) / 2 * S =
        ∑ i ∈ Finset.range (n+1), f i * g i := by
        have : ∑ i ∈ Finset.range (n+1), f i * g i =
          ∑ i ∈ Finset.range n, f i * g i + f n * g n := by
          exact Finset.sum_range_succ (fun x ↦ f x * g x) n
        rw [this]
        have h9 : ∑ i : Fin n, (↑i + 1) * y i = ∑ i : Fin n,f i * g i := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [f, g]
        have h10 : ∑ i : Fin n,f i * g i = ∑ i ∈ Finset.range n, f i * g i := by
          exact Eq.symm (Finset.sum_range fun i ↦ f i * g i)
        rw [h9, h10] ;simp [f,g]
      have h11 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (n+1)) f g
      have h12 : ∑ i ∈ Finset.range (n + 1), f i ^ 2 = ∑ i : Fin n, (↑↑i + 1) ^ 2 + (↑n * (↑n + 1) / 2) ^ 2 := by
        have : ∑ i : Fin n, ((↑i:ℝ) + 1) ^ 2 = ∑ i ∈ Finset.range n, ((↑i : ℝ) + 1) ^ 2 := by
          exact Eq.symm (Finset.sum_range fun i ↦ ((↑i : ℝ) + 1) ^ 2)
        rw [this] ;rw [Finset.sum_range_succ] ;simp [f]
        apply Finset.sum_congr rfl
        intro i hi ;simp at hi ;simp [hi]
      have h13 : ∑ i ∈ Finset.range (n + 1), g i ^ 2 = ∑ i : Fin n, y i ^ 2 + S ^ 2 := by
        have : ∑ i : Fin n, y i ^ 2 = ∑ i : Fin n, g i ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi ;simp [g]
        have h14 : ∑ i : Fin n, g i ^ 2 = ∑ i ∈ Finset.range n, g i ^ 2 := by
          exact Eq.symm (Finset.sum_range fun i ↦ g i ^ 2)
        rw [this,h14,Finset.sum_range_succ] ;simp [g]
      rw [h8,← h12,← h13] ;exact h11
    have h14 : ∑ i : Fin n, y i ^ 2 + S ^ 2 = ∑ i : Fin n, x i ^ 2 - (1 / (n + 1)) * (∑ i, x i)^2 := by
      rw [h4] ;ring
    rw [h14] at h7
    have h15 : ∑ i : Fin n, (↑↑i + 1) ^ 2 + (↑n * ((↑n :ℝ) + 1) / 2) ^ 2 =
      n * (n + 1) * (n + 2) * (3 * n + 1) / 12 := by
      have : ∑ i : Fin n, ((↑i :ℝ) + 1) ^ 2 = ∑ i ∈ Finset.range n, ((↑i :ℝ) + 1) ^ 2 := by
        exact Eq.symm (Finset.sum_range fun i ↦ ((↑i :ℝ) + 1) ^ 2)
      rw [this]
      have : ∀ m : ℕ , ∑ i ∈ Finset.range m, ((i + 1) ^ 2 : ℝ) = m * (m + 1) * (2*m + 1) / 6 := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [Finset.sum_range_succ,ih,Nat.cast_add] ;ring
      rw [this n] ;ring
    rw [h15] at h7
    have h16 : 0 < (↑n :ℝ) * (↑n + 1) * (↑n + 2) * (3 * ↑n + 1) / 12 := by
      have : 0 < (↑n : ℝ) := by
        exact Nat.cast_pos'.mpr hn
      nlinarith
    apply (div_le_iff₀' h16).mpr at h7
    apply le_sub_iff_add_le.mp at h7
    have h17 : (∑ i : Fin n, (↑↑i + 1) * x i) ^ 2 / (↑n * (↑n + 1) * (↑n + 2) * (3 * ↑n + 1) / 12)
      = (12 * (∑ i : Fin n, (↑↑i + 1) * x i) ^ 2) / (↑n * (↑n + 1) * (↑n + 2) * (3 * ↑n + 1)) := by
      rw [← div_mul] ;ring
    rw [h17] at h7
    linarith