import Mathlib

open Finset Lagrange Polynomial

/-For $1 \leq j \leq 2014$, define

$$
b_{j}=j^{2014} \prod_{i=1, i \neq j}^{2014}\left(i^{2014}-j^{2014}\right)
$$

where the product is over all $i \in\{1, \ldots, 2014\}$ except $i=j$. Evaluate

$$
\frac{1}{b_{1}}+\frac{1}{b_{2}}+\cdots+\frac{1}{b_{2014}}
$$-/
theorem algebra_609266 (b : ℕ → ℚ) (hb : ∀ j ∈ Icc 1 2014, b j =
    j ^ 2014 * ∏ i ∈ (Icc 1 2014).erase j, ((i : ℚ) ^ 2014 - j ^ 2014)) :
    ∑ i ∈ Icc 1 2014, 1 / b i = 1 / (Nat.factorial 2014) ^ 2014 := by
-- Generalize $2014$ to any even number greater than $1$
  have ngt : 1 < 2014 := by simp
  have npar : Even 2014 := by use 1007
  generalize 2014 = n at ngt hb npar
-- Set up a finset $s$, a nodal map $v$ and a value function $r$ in order to use Lagrange interpolation
  let s := Icc 1 n; let v : ℕ → ℚ := fun i => i ^ n
  let r : ℕ → ℚ := fun _ => 1
-- Prove that the interpolation of $s$, $v$ and $r$ is the constant function $1$
  have Itp1 : (C 1 : ℚ[X]) = interpolate s v r := by
    apply eq_interpolate_of_eval_eq
    · simp [v, s]; intro i _ j _ hij
      simp at hij; norm_cast at hij
      rw [pow_left_inj₀] at hij
      exact hij; all_goals positivity
    simp; use 1; simp [s]; omega
    simp [r]
-- Evaluate `Itp1` both sides at $0$ and simplify
  apply_fun fun t => t.eval 0 at Itp1
  rw [eval_C, eval_interpolate_not_at_node] at Itp1
  rw [nodal, eval_prod] at Itp1
  simp [nodalWeight, s, v, r, ← one_div, mul_one_div, div_div] at Itp1
-- Rearrange the summations and products, the goal follows
  have : (∏ x ∈ Icc 1 n, -(x:ℚ) ^ n) = n.factorial ^ n := by
    rw [← prod_Ico_id_eq_factorial, show Ico 1 (n+1) = Icc 1 n by rfl]
    rw [Nat.cast_prod, ← prod_pow]; calc
      _ = ∏ x ∈ Icc 1 n, (-1 : ℚ) * x ^ n := by
        apply prod_congr rfl; simp
      _ = _ := by
        rw [prod_mul_distrib, prod_const, Even.neg_one_pow, one_mul]
        simp; exact npar
  rw [this, mul_comm, ← div_eq_iff] at Itp1
  rw [Itp1]; apply sum_congr rfl
  intro i hi; rw [hb i hi]; congr
  rw [mul_comm, ← neg_mul, mul_right_cancel_iff_of_pos]
  symm; calc
    _ = ∏ x ∈ (Icc 1 n).erase i, -1*((i : ℚ) ^ n - x ^ n) := by
      rw [prod_mul_distrib, prod_const, neg_eq_neg_one_mul]
      congr; symm; apply Odd.neg_one_pow
      simp [card_erase_of_mem hi]; rcases npar with ⟨k, hk⟩
      use k-1; rw [hk]; zify; repeat rw [Nat.cast_sub]
      push_cast; ring; all_goals omega
    _ = _ := by
      apply prod_congr rfl; intros; ring
  simp at hi; rcases hi with ⟨⟩; positivity; positivity
  simp [s, v]; intros; positivity