import Mathlib

open Polynomial

/-
Let $b$ and $c$ be real numbers,
and define the polynomial $P(x) = x^{2} + bx + c$.
Suppose that $P(P(1)) = P(P(2)) = 0$, and that $P(1) \neq P(2)$.
Find $P(0)$.
-/

theorem algebra_609214 (b c : ℝ) (p : Polynomial ℝ)
    (hp : p = X^2 + C b * X + C c)
    (hp1 : p.eval (p.eval 1) = 0)
    (hp2 : p.eval (p.eval 2) = 0)
    (hp3 : p.eval 1 ≠ p.eval 2)
    : p.eval 0 = -3/2 := by
  -- First, evaluate $P(0), P(1)$ and $P(2)$. So we want to show $c = -3/2$.
  have p0 : p.eval 0 = c             := by simp_all
  have p1 : p.eval 1 = 1 + b + c     := by simp_all
  have p2 : p.eval 2 = 4 + 2 * b + c := by simp_all; linarith
  rw [p0]

  -- So these are the two distinct roots:
  let r := 1 + b + c
  have hr : r = p.eval 1 := by exact id (Eq.symm p1)
  have root1 : p.IsRoot r := by rw [← hr] at hp1; exact hp1

  let s := 4 + 2*b + c
  have hs : s = p.eval 2 := by exact id (Eq.symm p2)
  have root2 : p.IsRoot s := by rw [← hs] at hp2; exact hp2

  have distinct : r ≠ s := by rw [← hr, ← hs] at hp3; exact hp3

  -- We want to prove that $P(x) = (x - r)(x - s)$. There are many preliminaries.
  have pmonic : p.Monic := by rw [hp]; monicity <;> simp
  have deg2 : p.natDegree = 2 := by rw [hp]; compute_degree!
  have hpnz : p ≠ 0 := by intro h; simp [h] at deg2

  have two_roots : p.roots.card = 2 := by
    apply le_antisymm
    · rw [← deg2]
      apply card_roots'
    · rw [← Multiset.card_pair r s]
      apply Multiset.card_le_card
      simp only [Multiset.insert_eq_cons]
      rw [Multiset.cons_le_of_not_mem (by simp [distinct])]
      constructor
      · simpa [hpnz] using root1
      · simpa [hpnz] using root2

  have hroots : p.roots.card = p.natDegree := by simp_all

  have rootset : p.roots = {r, s} := by
    symm
    refine Multiset.eq_of_le_of_card_le ?_ ?_
    · rw [Multiset.le_iff_subset (by simp [distinct])]
      intro a ha
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
      obtain rfl | rfl := ha
      · simpa [hpnz] using root1
      · simpa [hpnz] using root2
    · rw [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton]
      suffices h : p.natDegree = 1 + 1 from h ▸ p.card_roots'
      subst hp
      compute_degree!

  -- Now we can prove $P(x) = (x-r)(x-s)$ finally!
  have prod1 := prod_multiset_X_sub_C_of_monic_of_roots_card_eq pmonic hroots
  have prod2 := by simp [rootset] at prod1; exact prod1

  -- Now we can substitute $r$ and $s$ in terms of $b,c$.
  have prod3 := by simp [r, s] at prod2; exact prod2
  have prod4 : p = X^2 + C (-5 - 3*b - 2*c) * X + C ((4 + 2*b + c)*(1 + b + c)) := by
    subst prod3
    simp only [map_add, map_mul, map_sub, map_neg, map_one, map_ofNat]
    ring

  -- Now we can compare coefficients and conclude $b = -(5+3b+2c)$
  -- and $c = (4 + 2b + c)(1 + b + c)$.
  let d := -5 - 3*b - 2*c
  let e := (4 + 2*b + c)*(1 + b + c)
  have prod5 : p = X^2 + C d * X + C e := prod4
  have coeffs : b = d ∧ c = e := by
    constructor
    . simpa using congr($(hp.symm.trans prod5).coeff 1)
    . simpa using congr($(hp.symm.trans prod5).coeff 0)

  have beq1 : b = -5 - 3*b - 2*c            := coeffs.left
  have ceq1 : c = (4 + 2*b + c)*(1 + b + c) := coeffs.right

  -- Solving the first equation we get $c = -5/2 - 2b$
  have ceq2 : c = -5/2 - 2*b := by linarith

  -- Plugging this into the second equation and solving for $b$
  -- we get $b = -1/2$ and $c = -3/2$.
  have beq2 : b = -1/2 := by rw [ceq2] at ceq1; linarith
  linarith
