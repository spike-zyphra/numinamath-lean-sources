import Mathlib

open Polynomial

/-The quadratic equation $ax^2+20x+c=0$ has exactly one solution. If $a+c=29$, and $a< c$ find the ordered pair $(a,c)$.

The final answer is $ \boxed{(4,25)} $-/
theorem algebra_10570 {a c : ℝ} (ha : a ≠ 0)
  (h : (C a * X^2 + C 20 * X + C c).roots = {x1, x1})
  (h1 : a + c = 29) (h2 : a < c) : (a, c) = (4, 25) := by
    -- We need Vieta's formula here.
    -- Factor quadratic polynomial.
    have hquadratic_factor {a b c x1 x2 : ℝ} (hroots : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2}) :
    C a * X ^ 2 + C b * X + C c = C a * (X - C x1) * (X - C x2) := by
      letI p : ℝ[X] := C a * X ^ 2 + C b * X + C c
      have hp_natDegree_eq_two : p.natDegree = 2 := by
        apply le_antisymm
        . exact natDegree_quadratic_le
        convert Polynomial.card_roots' p
        rw [hroots, Multiset.card_pair]
      have hp_natDegree_eq_roots_card : Multiset.card p.roots = p.natDegree := by
        rw [hroots, Multiset.card_pair, hp_natDegree_eq_two]
      haveI := C_leadingCoeff_mul_prod_multiset_X_sub_C hp_natDegree_eq_roots_card
      convert this.symm using 1
      rw [leadingCoeff, hp_natDegree_eq_two]
      simpa [p, hroots] using by ac_rfl
  -- Vieta's formula
    have hquadratic_vieta {a b c x1 x2 : ℝ} (hroots : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2}) :
        -a * (x1 + x2) = b ∧ a * x1 * x2 = c := by
        letI p : ℝ[X] := C a * X ^ 2 + C b * X + C c
        have hp_factor := hquadratic_factor hroots
        have hp_expand : C a * (X - C x1) * (X - C x2) = C a * X ^ 2 + C (-a * (x1 + x2)) * X + C (a * x1 * x2) := by
          simp only [C_neg, C_add, C_mul]
          ring
        constructor
        . apply_fun (·.coeff 1) at hp_factor
          convert hp_factor.symm
          simp [hp_expand]
          simp
        apply_fun (·.coeff 0) at hp_factor
        convert hp_factor.symm
        simp
        simp
    -- using vitea formula, we get $-a(x1 + x1) = 20$ and $ax1x1 = c$.
    have ⟨c1, c2⟩ := hquadratic_vieta h
    replace c1 : a * x1 = -10 := by linarith
    have x1ne0 : x1 ≠ 0 := by
      intro x10; simp [x10] at c1
    rw [c1] at c2
    replace c1 : a = -10 / x1 := (eq_div_iff_mul_eq x1ne0).2 c1
    rw [c1, ←c2] at h1
    -- Because $a + c = 29$, so  10 * x1^2 + 29 * x1 + 10 = 0.
    have c3 : 10 * x1^2 + 29 * x1 + 10 = 0 := by
      apply_fun (· * x1) at h1
      simp [add_mul, x1ne0] at h1
      nlinarith
    replace c3 : 10 * (x1 + 10/4) * (x1 + 4/10) = 0 := by nlinarith
    simp at c3
    -- Solving this equation, we get $x1 = -10 / 4$ or $x1 = - 4 /10$.
    rcases c3 with c3 | c3
    · -- Case1 : x1 = - 10 / 4 : Substitute x1 by -10/4 we get $a = 4$ and $c = 25$.
      have : x1 = - 10 / 4 := by linarith
      simp [this] at c1 c2
      ring_nf at c1 c2
      ext <;> simp [c1, c2]
    · -- Case2 : x1 = - 4 / 10 : Substitute x1 by -4/10 we get $a = 25$ and $c = 4$, which
      -- contradict with $a < c$.
      have : x1 = - 4 / 10 := by linarith
      simp [this] at c1 c2
      ring_nf at c1 c2
      simp [c1, ←c2] at h2
      norm_num at h2
