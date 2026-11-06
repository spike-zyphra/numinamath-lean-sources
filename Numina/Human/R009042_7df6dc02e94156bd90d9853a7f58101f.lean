import Mathlib

open Polynomial

/-Let $a$ and $b$ be real numbers, and let $r, s$, and $t$ be the roots of $f(x)=x^{3}+a x^{2}+b x-1$. Also, $g(x)=x^{3}+m x^{2}+n x+p$ has roots $r^{2}, s^{2}$, and $t^{2}$. If $g(-1)=-5$, find the maximum possible value of $b$.-/
theorem algebra_609074 : let S := {(a, b) : ℝ × ℝ| ∀ r s t : ℂ,
    ((X : ℂ[X]) ^ 3 + C (a : ℂ) * X ^ 2 + C (b : ℂ) * X - C 1).roots = {r, s, t} →
    ∃ g : ℂ [X], g.natDegree = 3 ∧ g.Monic ∧ g.roots = {r ^ 2, s ^ 2, t ^ 2} ∧ g.eval (-1) = -5};
    IsGreatest {b : ℝ| ∃ a : ℝ, (a, b) ∈ S} (1 + √5) := by
-- It suffices to show that the set $S$ is of the following form
  intro S; suffices : S = {(a, b) : ℝ × ℝ| (a + 1) ^ 2 + (b - 1) ^ 2 = 5}
  · simp [this, IsGreatest, upperBounds]; constructor
    · use -1; simp
    intro b a hab; rw [← sub_le_iff_le_add']
    apply Real.le_sqrt_of_sq_le
    linarith only [hab, show 0 ≤ (a + 1) ^ 2 by positivity]
  simp [S, Set.ext_iff]; intro a b
  constructor
  -- Assume $(a,b)$ is in $S$, denote $f$ to be the complex polynomial in question and prove some basic properties of $f$
  · intro h; let f : ℂ[X] := X ^ 3 + C (a : ℂ) * X ^ 2 + C (b : ℂ) * X - 1
    have fdeg : f.natDegree = 3 := by
      dsimp [f]; compute_degree; all_goals norm_num
    have fmoni : f.Monic := by
      rw [Monic, leadingCoeff, fdeg]
      dsimp[f]; compute_degree
      all_goals norm_num
    have fsp : f.Splits (RingHom.id ℂ) := by exact IsAlgClosed.splits f
    have : f.roots.card = 3 := by
      rw [← fdeg, ← splits_iff_card_roots]
      exact fsp
    rw [Multiset.card_eq_three] at this; rcases this with ⟨r, s, t, frt⟩
    simp at frt; dsimp [f] at frt
  -- Rewrite $f$ as a product of linear polynomials and compare the coefficients on both sides
    have fprd := eq_prod_roots_of_monic_of_splits_id fmoni fsp
    simp [f, frt, ← mul_assoc] at fprd
    have : (X - C r) * (X - C s) * (X - C t) = X ^ 3 - (C r + C s + C t) * X ^ 2
    + (C r * C s + C s * C t + C t * C r) * X - C r * C s * C t := by ring
    rw [this] at fprd; simp [f, ext_iff] at fprd
    have c0 := fprd 0; have c1 := fprd 1; have c2 := fprd 2
    simp at c0 c1 c2; rw [show (1:ℂ[X]) = C 1 by rfl, coeff_C] at c1 c2
    rw [coeff_X] at c2; simp at c1 c2
    repeat rw [← C_add] at c1 c2
    rw [coeff_C_mul_X_pow] at c1 c2; simp at c1 c2
  -- Specialize the assumption $h$ at the roots of $f$, we obtain a polynomial $g$ with certain properties
    specialize h r s t frt; rcases h with ⟨g, ⟨gdeg, gmoni, grt, gevm1⟩⟩
    have gsp : g.Splits (RingHom.id ℂ) := by exact IsAlgClosed.splits g
    have gprd := eq_prod_roots_of_monic_of_splits_id gmoni gsp
    simp [grt, ← mul_assoc] at gprd; rw [← neg_eq_iff_eq_neg] at gevm1
  -- The goal follows from rewriting $5$ to $-eval (-1) g$ and use the product form of $g$ to compute the evaluation
    rw [← Complex.ofReal_inj]; push_cast
    rw [← sub_eq_zero, ← gevm1, gprd, c1, c2]; simp
    ring_nf; calc
      _ = 1 - r * 2 - s * 2 - t * 2 + (r * s * t) * (2 * r + 2 * s + 2 * t - r * s * t) := by ring
      _ = _ := by rw [← c0]; ring
-- Conversely, suppose we have $(a, b)$ satisfying the equation, we need to construct $g$ with required properties
  intro hab r s t frt; let f : ℂ[X] := X ^ 3 + C (a : ℂ) * X ^ 2 + C (b : ℂ) * X - 1
  have fdeg : f.natDegree = 3 := by
    dsimp [f]; compute_degree; all_goals norm_num
  have fmoni : f.Monic := by
    rw [Monic, leadingCoeff, fdeg]
    dsimp[f]; compute_degree
    all_goals norm_num
  have fsp : f.Splits (RingHom.id ℂ) := by exact IsAlgClosed.splits f
-- Rewrite $f$ to a product of linear polynomials and compare coefficients on both sides
  have fprd := eq_prod_roots_of_monic_of_splits_id fmoni fsp
  simp [f, frt, ← mul_assoc] at fprd
  have : (X - C r) * (X - C s) * (X - C t) = X ^ 3 - (C r + C s + C t) * X ^ 2
  + (C r * C s + C s * C t + C t * C r) * X - C r * C s * C t := by ring
  rw [this] at fprd; simp [f, ext_iff] at fprd
  have c0 := fprd 0; have c1 := fprd 1; have c2 := fprd 2
  simp at c0 c1 c2; rw [show (1:ℂ[X]) = C 1 by rfl, coeff_C] at c1 c2
  rw [coeff_X] at c2; simp at c1 c2
  repeat rw [← C_add] at c1 c2
  rw [coeff_C_mul_X_pow] at c1 c2; simp at c1 c2
-- Denote $g$ to be the product $(x-r^2)(x-t^2)(x-s^2)$ and prove some basic properties of $g$
  let g := (X - C (r ^ 2)) * (X - C (s ^ 2)) * (X - C (t ^ 2))
  have geq : g = X ^ 3 - (C (r ^ 2)+ C (s ^ 2) + C (t ^ 2)) * X ^ 2
  + (C (r ^ 2) * C (s ^ 2) + C (s ^ 2) * C (t ^ 2) + C (t ^ 2) * C (r ^ 2)) * X - C (r ^ 2) * C (s ^ 2) * C (t ^ 2) := by ring
  have gdeg : g.natDegree = 3 := by
    rw [geq]; compute_degree; all_goals norm_num
  have gmoni : g.Monic := by
    rw [Monic, leadingCoeff, gdeg, geq]
    compute_degree; all_goals norm_num
  have grt : g.roots = r ^ 2 ::ₘ s ^ 2 ::ₘ {t ^ 2} := by
    dsimp [g]; repeat rw [roots_mul, roots_X_sub_C]
    rw [roots_X_sub_C]; simp
    apply mul_ne_zero; any_goals apply X_sub_C_ne_zero
    apply mul_ne_zero; apply mul_ne_zero
    all_goals apply X_sub_C_ne_zero
  use g; split_ands; any_goals assumption
-- Prove that evaluating $g$ at $-1$ is $-5$, therefore $g$ is a desired polynomial
  rw [← Complex.ofReal_inj] at hab; push_cast at hab
  rw [← hab, ← sub_eq_zero, c1, c2]; simp [g]
  ring_nf; calc
      _ = 1 - r * 2 - s * 2 - t * 2 + (r * s * t) * (2 * r + 2 * s + 2 * t - r * s * t) := by ring
      _ = _ := by rw [← c0]; ring