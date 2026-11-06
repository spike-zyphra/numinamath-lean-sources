import Mathlib

open Polynomial Complex Finset

/-Let $z_{1}, z_{2}, z_{3}, z_{4}$ be the solutions to the equation $x^{4}+3 x^{3}+3 x^{2}+3 x+1=0$. Then $\left|z_{1}\right|+\left|z_{2}\right|+\left|z_{3}\right|+\left|z_{4}\right|$ can be written as $\frac{a+b \sqrt{c}}{d}$, where $c$ is a square-free positive integer, and $a, b, d$ are positive integers with $\operatorname{gcd}(a, b, d)=1$. Compute $1000 a+100 b+10 c+d$.-/
theorem algebra_610444 : let p : ℂ[X] := X ^ 4 + C 3 * X ^ 3 + C 3 * X ^ 2 + C 3 * X + 1
    ∃ a b c d : ℕ, (Multiset.map (fun z => ‖z‖) p.roots).sum  = (a + b * √c) / d ∧
    Squarefree c ∧ (a.gcd b).gcd d = 1 ∧ 1000 * a + 100 * b + 10 * c + d = 7152 := by
-- Prove that the polynomial in question is monic of degree $4$
  intro p; have pdeg : p.natDegree = 4 := by
    dsimp [p]; compute_degree
    all_goals simp
  have pmoni : p.Monic := by
    rw [Monic, leadingCoeff, pdeg]
    dsimp [p]; compute_degree
    all_goals simp
-- Denote the following two monic quadratic polynomials to be $p1$ and $p2$
  let p1 := (X ^ 2 + C (3 / 2) * X + 1 + C ((√5 : ℂ) / 2) * X)
  let p2 := (X ^ 2 + C (3 / 2) * X + 1 - C ((√5 : ℂ) / 2) * X)
  have p1deg : p1.natDegree = 2 := by
    dsimp [p1]; compute_degree
    all_goals simp
  have p2deg : p2.natDegree = 2 := by
    dsimp [p2]; compute_degree
    all_goals simp
  have moni1 : p1.Monic := by
    rw [Monic, leadingCoeff, p1deg]
    dsimp [p1]; compute_degree
    all_goals simp
  have moni2 : p2.Monic := by
    rw [Monic, leadingCoeff, p2deg]
    dsimp [p2]; compute_degree
    all_goals simp
-- Prove that $p=p1*p2$
  have fac : p = p1 * p2 := by
    rw [← sq_sub_sq, mul_pow, ← C_pow, div_pow]
    norm_num [← ofReal_pow]; dsimp [p]; ring_nf
    nth_rw 6 [add_assoc]; rw [← mul_sub, ← mul_add]
    rw [mul_assoc, mul_assoc]; congr
    · rw [show (2:ℂ[X]) = C 2 by rfl]
      norm_num [← C_mul]
    · rw [show (2:ℂ[X]) = C 2 by rfl]
      rw [← C_pow, ← C_sub, ← C_add]; norm_num
    rw [show (2:ℂ[X]) = C 2 by rfl]
    norm_num [← C_mul]
-- Split the sum in the goal according to `fac` and write out the Vieta's theorem for roots of $p1$ and $p2$
  rw [fac, roots_mul, Multiset.map_add, Multiset.sum_add]
  have p1rt : p1.roots.card = 2 := by
    rw [← p1deg, ← splits_iff_card_roots]
    exact IsAlgClosed.splits p1
  have p2rt : p2.roots.card = 2 := by
    rw [← p2deg, ← splits_iff_card_roots]
    exact IsAlgClosed.splits p2
  rw [Multiset.card_eq_two] at p1rt p2rt
  rcases p1rt with ⟨u, v, huv⟩; rcases p2rt with ⟨u', v', huv'⟩
  have prod1 := eq_prod_roots_of_monic_of_splits_id moni1 (IsAlgClosed.splits p1)
  have prod2 := eq_prod_roots_of_monic_of_splits_id moni2 (IsAlgClosed.splits p2)
  simp [huv] at prod1; simp [huv'] at prod2
  rw [mul_sub, sub_mul, sub_mul] at prod1 prod2
  rw [Polynomial.ext_iff_natDegree_le (show p1.natDegree≤2 by simp [p1deg])] at prod1
  rw [Polynomial.ext_iff_natDegree_le (show p2.natDegree≤2 by simp [p2deg])] at prod2
  have ceq1 := prod1 0; simp [p1] at ceq1
  have ceq2 := prod2 0; simp [p2] at ceq2
  specialize prod1 1; simp [p1] at prod1
  specialize prod2 1; simp [p2] at prod2
  rw [show (1:ℂ[X]) = C 1 by rfl, coeff_C_ne_zero, add_zero] at prod1 prod2
-- Compute the sum of norms of the roots of $p1$ and $p2$ respectively
  simp [Complex.ext_iff] at ceq1 ceq2 prod1 prod2
  rcases ceq1 with ⟨ceq1l, ceq1r⟩; rcases ceq2 with ⟨ceq2l, ceq2r⟩
  rcases prod1 with ⟨prod1l, prod1r⟩; rcases prod2 with ⟨prod2l, prod2r⟩
  symm at prod1r prod2r; rw [sub_eq_zero, neg_eq_iff_eq_neg] at prod1r prod2r
  rw [prod1r, neg_mul, ← sub_eq_add_neg, mul_comm] at ceq1r
  rw [prod2r, neg_mul, ← sub_eq_add_neg, mul_comm] at ceq2r
  norm_num [← mul_sub] at ceq1r ceq2r; rw [or_comm] at ceq1r
  rcases ceq1r with ceq1r|ceq1r
  -- If $u.re-v.re$, we can derive a contradiction from linear arithmetic
  · rw [sub_eq_zero] at ceq1r; rw [ceq1r] at prod1l
    rw [prod1r, ceq1r, ← pow_two, neg_mul, ← pow_two, sub_neg_eq_add] at ceq1l
    exfalso; have : v.re ^ 2 ≤ 1 := by
      rw [ceq1l, le_add_iff_nonneg_right]
      positivity
    convert this; simp [show v.re = -3/4-√5/4 by linarith only [prod1l]]
    rw [abs_eq_neg_self.mpr]; suffices : 1 < √5
    · linarith only [this]
    rw [Real.lt_sqrt]; any_goals norm_num
    rw [neg_le_iff_add_nonneg]; positivity
  rcases ceq2r with ceq2r|ceq2r
  -- If $v'.im=0$, we can derive a contradiction from linear arithmetic
  · simp [ceq2r] at prod2r; simp [ceq2r, prod2r] at ceq2l
    exfalso; have : 0 ≤ (u'.re - v'.re) ^ 2 := by positivity
    convert this; simp; calc
      _ = (-u'.re - v'.re) ^ 2 - 4 * (u'.re * v'.re) := by ring
      _ < _ := by
        rw [← prod2l, ← ceq2l]; ring_nf
        norm_num; rw [← neg_pos]; ring_nf; positivity
  rw [sub_eq_zero] at ceq2r; rw [ceq2r] at prod2l ceq2l
  rw [prod2r, neg_mul, sub_neg_eq_add, ← pow_two, ← pow_two] at ceq2l
  simp [ceq1r] at prod1r; simp [ceq1r, prod1r] at ceq1l
  simp [huv, huv', abs_eq_sqrt_sq_add_sq, ceq1r, prod1r]
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  rw [abs_eq_neg_self.mpr, abs_eq_neg_self.mpr, ← sub_eq_add_neg, ← prod1l]
  rw [prod2r, neg_sq, ceq2r, ← ceq2l]; ring_nf
-- Use $a=7$, $b=1$, $c=5$ and $d=2$ to fulfill the goal and finish the computations
  use 7, 1, 5, 2; norm_num; constructor
  · ring
  exact Nat.prime_five.squarefree
  · by_contra! h; replace prod1l : 0 < -u.re - v.re := by
      rw [← prod1l]; positivity
    have : u.re < 0 := by linarith only [h, prod1l]
    replace this : u.re * v.re < 0 := mul_neg_of_neg_of_pos this h
    linarith only [ceq1l, this]
  · by_contra! h; replace prod1l : 0 < -u.re - v.re := by
      rw [← prod1l]; positivity
    have : v.re < 0 := by linarith only [h, prod1l]
    replace this : u.re * v.re < 0 := mul_neg_of_pos_of_neg h this
    linarith only [ceq1l, this]
  any_goals norm_num
  any_goals compute_degree
  constructor; intro h; simp [h] at p1deg
  intro h; simp [h] at p2deg