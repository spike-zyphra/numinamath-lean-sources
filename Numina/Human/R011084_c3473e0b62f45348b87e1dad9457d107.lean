import Mathlib

open Polynomial Set

/-During the car ride home, Michael looks back at his recent math exams. A problem on Michael's calculus mid-term gets him starting thinking about a particular quadratic,\[x^2-sx+p,\]with roots $r_1$ and $r_2$. He notices that\[r_1+r_2=r_1^2+r_2^2=r_1^3+r_2^3=\cdots=r_1^{2007}+r_2^{2007}.\]He wonders how often this is the case, and begins exploring other quantities associated with the roots of such a quadratic. He sets out to compute the greatest possible value of\[\dfrac1{r_1^{2008}}+\dfrac1{r_2^{2008}}.\]Help Michael by computing this maximum.-/
theorem algebra_13364 {s p : ℝ} (h1 : (C 1 * X^2 + C (-s) * X + C p).roots = {r1, r2})
  (hr1 : r1 ≠ 0) (hr2 : r2 ≠ 0) (h2 : ∀ i ∈ Icc 1 2007, r1 + r2 = r1^i + r2^i) :
  IsGreatest {k | k = 1 / r1 ^ 2008 + 1 / r2 ^ 2008 } 2 := by
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
    -- By Vieta's Formulas, $r_1 + r_2 = s$ and $r_1 * r_2 = p$.
    have := hquadratic_vieta h1
    have ⟨c1, c2⟩ : r1 + r2 = s ∧ r1 * r2 = p := by constructor <;> nlinarith
    -- That means $r_1^2 + r_2^2 = s^2 - 2p = s$ and
    -- $r_1^3 + r_1^3 = (r_1 + r_2)^3 - 3r_1^2r_2 - 3r_1r_2^2 = s^3 - 3ps$.
    have c3 : s = s^2 - 2*p := by
      have := h2 2 (by simp)
      have : r1 + r2 = (r1 + r2)^2 - 2 *r1*r2 := by nlinarith
      simp [mul_assoc, c1, c2] at this
      simp [←this]
    have c4 : s = s^3 - 3*p*s := by
      have := h2 3 (by simp)
      have : r1 + r2 = (r1 + r2)^3 - 3*(r1*r2)*(r1 + r2) := by nlinarith
      simp [c1, c2] at this
      exact this
    -- Note that $s = s^2 - 2p$, so $p = \frac{s^2 - s}{2}$. We also know that $s = s^3 - 3ps$, so substituting for $p$ results in
    -- \begin{align*} s &= s^3 - 3s \cdot \frac{s^2 - s}{2} \\ s &= s^3 - \tfrac32 s^3 + \tfrac32 s^2 \\ 0 &= -\tfrac12 s^3 + \tfrac32 s^2 - s \\ 0 &= s^3 - 3s^2 + 2s \\ &= s(s-2)(s-1) \end{align*}
    have : s * (s - 1) * (s - 2) = 0 := by nlinarith
    -- Thus, $s = 0,1,2$.
    have hs : (s = 0 ∨ s = 1) ∨ s = 2 := by
      rcases mul_eq_zero.1 this with h | h <;> norm_num at h
      · rcases h with h | h
        · tauto
        · have : s = 1 := by linarith
          tauto
      · have : s = 2 := by linarith
        tauto
    have hp : p = s * (s - 1) / 2 := by nlinarith
    rcases hs with s01 | s2
    · -- If $s = 1$ or $s = 0$, then $p = 0$. However, both cases result in one root being zero,
      -- so $\dfrac1{r_1^{2008}}+\dfrac1{r_2^{2008}}$ is undefined.
      have : p = 0 := by
        rcases s01 with s01 | s01 <;> simp [s01] at hp <;> tauto
      rw [this, mul_eq_zero] at c2
      tauto
    · -- If $s = 2$, then $p = 1$, making both roots equal to $1$.
      -- Thus, $\dfrac1{r_1^{2008}}+\dfrac1{r_2^{2008}} = 1+1 = \boxed{2}$.
      simp [s2] at hp
      norm_num at hp
      simp [s2, hp] at c1 c2
      have ⟨r11, r21⟩ : r1 = 1 ∧ r2 = 1 := by split_ands <;> nlinarith
      simp [r11, r21, IsGreatest]
      split_ands <;> ring_nf; linarith
