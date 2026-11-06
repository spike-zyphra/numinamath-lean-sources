import Mathlib

open Polynomial

/- Let $f(x)=x^{3}+x+1$. Suppose $g$ is a cubic polynomial such that $g(0)=-1$, and the roots of $g$ are the squares of the roots of $f$. Find $g(9)$.-/
theorem algebra_608256 {a b c : ℂ} {f g : ℂ[X]} (hf : f = X ^ 3 + X + C 1) (hfroots : f.roots = {a, b, c})
    (hg_natDegree : g.natDegree = 3) (hg0 : g.eval 0 = -1) (hgroots : g.roots = {a ^ 2, b ^ 2, c ^ 2}) :
    g.eval 9 = 899 := by
  -- Need the following facts to factor `f(x)` and `g(x)`.
  -- It's clear that degree of `f(x)` is `3`.
  have hf_natDegree : f.natDegree = 3 := by rw [hf]; compute_degree!
  -- It's clear that `f(x)` is monic.
  have hfmonic : f.Monic := by
    rw [Monic, leadingCoeff, hf_natDegree, hf, coeff_add, coeff_add, coeff_X, coeff_C]
    norm_num
  -- It's clear that `f(x)` has `3` roots.
  have hfroots_card : Multiset.card f.roots = f.natDegree := by rw [hf_natDegree]; simp [hfroots]
  -- It's clear that `g(x)` has `3` roots.
  have hgroots_card : Multiset.card g.roots = g.natDegree := by rw [hg_natDegree]; simp [hgroots]
  -- Factor `f(x)`.
  have ffactor := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hfmonic hfroots_card
  -- Factor `g(x)`.
  have gfactor := C_leadingCoeff_mul_prod_multiset_X_sub_C hgroots_card
  -- Let $a, b, c$ be the zeros of $f$.
  -- Then $f(x)=(x-a)(x-b)(x-c)$.
  replace ffactor : (X - C a) * (X - C b) * (X - C c) = f := by
    convert ffactor
    simp [hfroots]
    ring
  -- Then, the roots of $g$ are $a^{2}, b^{2}, c^{2}$,
  -- so $g(x)=k\left(x-a^{2}\right)\left(x-b^{2}\right)\left(x-c^{2}\right)$ for some constant $k$.
  replace gfactor : C g.leadingCoeff * ((X - C (a ^ 2)) * (X - C (b ^ 2)) * (X - C (c ^ 2))) = g := by
    convert gfactor
    simp [hgroots]
    ring
  -- Since $a b c=-f(0)=-1$, we have $k=k a^{2} b^{2} c^{2}=-g(0)=1$. Thus,
  have hg_leadingCoeff : g.leadingCoeff = 1 := by
    have hf0 : f.eval 0 = 1 := by simp [hf]
    have : g.eval 0 = -g.leadingCoeff * f.eval 0 ^ 2 := by
      conv => congr; rw [← gfactor]; rfl; rhs; rw [← ffactor]
      simp; left; ring
    rw [hg0, hf0] at this
    linear_combination this
  -- $$ g\left(x^{2}\right)=\left(x^{2}-a^{2}\right)\left(x^{2}-b^{2}\right)\left(x^{2}-c^{2}\right)=
  -- (x-a)(x-b)(x-c)(x+a)(x+b)(x+c)=-f(x) f(-x) $$
  have hg_eval_sq_eq_mul_f_eval (x : ℂ) : g.eval (x ^ 2) = - f.eval x * f.eval (-x) := by
    rw [hg_leadingCoeff] at gfactor
    rw [← gfactor, ← ffactor]
    simp; ring
  -- Setting $x=3$ gives $g(9)=-f(3) f(-3)=-(31)(-29)=899$.
  rw [show (9 : ℂ) = 3 ^ 2 by norm_num, hg_eval_sq_eq_mul_f_eval]
  simp [hf]; norm_num
