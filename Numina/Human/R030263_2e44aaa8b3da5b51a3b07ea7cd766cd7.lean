import Mathlib
open Real
example {a b : ℝ} (h : b ≠ 0) : a * b / b = a := by exact mul_div_cancel_right₀ a h

/- [ $\left.\quad \begin{array}{ll}\text { Convexity and Concavity }\end{array}\right]$

Prove the inequalities:

a) $n\left(x_{1}+\ldots+x_{n}\right) \geq\left(\sqrt{x_{1}}+\ldots+\sqrt{x_{n}}\right)^{2}$

b) $\frac{n^{3}}{\left(x_{1}+\ldots+x_{n}\right)^{2}} \leq \frac{1}{x_{1}^{2}}+\ldots+\frac{1}{x_{n}^{2}}$

c) $n x_{1} \ldots x_{n} \leq x_{1}^{n}+\ldots+x_{n}^{n}$

d) $\left(x_{1}+\ldots+x_{n}\right)\left(\frac{1}{x_{1}}+\ldots+\frac{1}{x_{n}}\right) \geq n^{2}$ (Minkowski's inequality).

The values of the variables are assumed to be positive. -/
theorem inequalities_170848 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) :
    n * ∑ i, x i ≥ (∑ i, sqrt (x i)) ^ 2 ∧
    n ^ 3 / (∑ i, x i) ^ 2 ≤ ∑ i, 1 / (x i) ^ 2 ∧
    n * ∏ i, x i ≤ ∑ i, (x i) ^ n ∧
    (∑ i, x i) * (∑ i, 1 / x i) ≥ n ^ 2 := by
    have n_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have hn_inv : n * (↑n)⁻¹ = (1 : ℝ) := by exact mul_inv_cancel₀ (by exact_mod_cast hn.ne.symm)
    -- define the weights for the Jensen inequality
    set w := fun (i : Fin n) ↦ ((1 / n) : ℝ) with hw
    -- prove some things about these weights
    have w_pos : ∀ i ∈ Finset.univ, 0 < w i := fun i hi ↦ Nat.one_div_cast_pos hn.ne.symm
    have w_sum : ∑ i, w i = 1
    · rw [Finset.sum_const]
      simp only [Finset.card_univ, Fintype.card_fin, one_div, nsmul_eq_mul]
      exact hn_inv
    have mem_nonneg : ∀ i ∈ Finset.univ, x i ∈ Set.Ici 0 := fun i hi ↦ (hx i).le
    have pos_sum : 0 < ∑ i, w i • x i
    · apply Finset.sum_pos
      intro i hi
      apply smul_pos (w_pos i hi) (hx i)
      apply Finset.card_pos.mp
      simp only [Finset.card_univ, Fintype.card_fin]
      exact hn
    constructor

    -- (a) : use t ↦ √t
    · have pos_sum_sqrt : 0 ≤ ∑ i, w i • √(x i)
      · apply Finset.sum_nonneg
        intro i hi
        exact smul_nonneg' (w_pos i hi).le (sqrt_nonneg _)
      have jensen' := ConcaveOn.le_map_sum Real.strictConcaveOn_sqrt.concaveOn
        (fun i hi ↦ (w_pos i hi).le)
        w_sum
        (show ∀ i ∈ Finset.univ, x i ∈ Set.Ici 0 by intro i hi; exact (hx i).le)
      have jensen' := pow_le_pow_left₀ pos_sum_sqrt jensen' 2
      rw [sq_sqrt pos_sum.le, hw] at jensen'
      simp at jensen'
      rw [←Finset.mul_sum, ←Finset.mul_sum] at jensen'
      have jensen := mul_le_mul_of_nonneg_left jensen' (sq_nonneg (↑ n))
      ring_nf at jensen
      convert jensen.ge
      · rw [pow_two, mul_self_mul_inv]
      · conv_lhs => rw [←one_mul ((∑ i, √(x i)) ^ 2)]
        congr
        rw [pow_two, pow_two, ←mul_assoc _ (n⁻¹ : ℝ), mul_self_mul_inv]
        exact hn_inv.symm

    -- (b) use t ↦ 1/t^2
    constructor
    · have convex : ConvexOn ℝ (Set.Ioi 0) (fun (t : ℝ) ↦ t^(-2 : ℤ)) := convexOn_zpow _
      have recip_pow2 : ∀ (t : ℝ), 0 ≠ t → t^(-2 : ℤ) = 1 / t^(2 : ℤ)
      · intro t ht
        apply (eq_one_div_of_mul_eq_one_left _)
        exact zpow_neg_mul_zpow_self 2 ht.symm
      have mem_pos : ∀ i ∈ Finset.univ, x i ∈ Set.Ioi 0 := fun i hi ↦ hx i
      have jensen' := ConvexOn.map_sum_le convex (fun i hi ↦ (w_pos i hi).le) w_sum mem_pos
      rw [recip_pow2 _ pos_sum.ne] at jensen'
      conv_rhs at jensen' => arg 2; intro i; rw [recip_pow2 _ (hx i).ne]
      rw [hw] at jensen'
      simp at jensen'
      rw [←Finset.mul_sum, ←Finset.mul_sum] at jensen'
      have jensen := mul_le_mul_of_nonneg_left jensen' n_pos.le
      field_simp at jensen
      convert jensen
      exact_mod_cast pow_succ' _ _

    -- (c) use t ↦ exp(n * t)
    constructor
    · let mul_n := fun (t : ℝ) ↦ n * t
      have mul_n_range : (mul_n '' Set.univ) = Set.univ
      · ext y; simp [mul_n]; use (↑n)⁻¹ * y; rw [←mul_assoc, hn_inv, one_mul]
      have mul_convex : ConvexOn ℝ Set.univ mul_n :=
        ⟨convex_univ, fun x hx y hy a b ha hb hab ↦ by simp [mul_n]; linarith [hn]⟩
      have convex : ConvexOn ℝ Set.univ (exp ∘ mul_n)
      · apply ConvexOn.comp _ mul_convex _
        all_goals rw [mul_n_range]
        exact convexOn_exp
        rw [monotoneOn_univ]
        exact exp_monotone
      have jensen' := ConvexOn.map_sum_le convex
        (fun i hi ↦ (w_pos i hi).le)
        w_sum
        (show ∀ i ∈ Finset.univ, log (x i) ∈ Set.univ by intro i hi; exact trivial)
      simp [mul_n, hw] at jensen'
      rw [←Finset.mul_sum, ←Finset.mul_sum, ←mul_assoc, hn_inv, one_mul, exp_sum] at jensen'
      conv_lhs at jensen' => enter [2, i]; rw [exp_log (hx i)]
      conv_rhs at jensen' => enter [2, 2, i]; rw [←log_rpow (hx i), exp_log (rpow_pos_of_pos (hx i) _)]
      have jensen := mul_le_mul_of_nonneg_left jensen' n_pos.le
      rw [←mul_assoc, hn_inv, one_mul] at jensen
      convert jensen
      simp only [rpow_natCast, mul_n]
    -- (d) use t ↦ 1/t
    · have inv_convex : ConvexOn ℝ (Set.Ioi 0) (fun (t : ℝ) ↦ t^(-1 : ℤ)) := by exact convexOn_zpow _
      have jensen' := ConvexOn.map_sum_le inv_convex
        (fun i hi ↦ (w_pos i hi).le)
        w_sum
        (show ∀ i ∈ Finset.univ, x i ∈ Set.Ioi 0 by intro i hi; exact hx i)
      simp [hw] at jensen'
      rw [←Finset.mul_sum, ←Finset.mul_sum] at jensen'
      have x_sum_pos : ∑ i, x i > 0
      · apply Finset.sum_pos (fun i hi ↦ hx i)
        apply Finset.card_pos.mp
        simp only [Finset.card_univ, Fintype.card_fin]
        exact hn
      have jensen := mul_le_mul_of_nonneg_left jensen' (mul_nonneg n_pos.le x_sum_pos.le)
      field_simp at jensen
      rw [
        mul_comm, ←mul_assoc, mul_div_assoc, div_self x_sum_pos.ne.symm, mul_one, ←pow_two,
        mul_assoc, mul_comm, mul_div_cancel_right₀ _ n_pos.ne.symm
      ] at jensen
      exact jensen.ge