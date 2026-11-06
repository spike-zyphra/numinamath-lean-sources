import Mathlib

open Set

/-
Let $S$ be the set of real numbers greater than -1 . Find all functions $f: S \rightarrow S$ such that

\[ f(x+f(y)+x f(y))=y+f(x)+y f(x) \quad \text { for all } x \text { and } y \text { in } S, \]
and $f(x) / x$ is strictly increasing for $-1 < x<0$ and for $0 < x$.
-/
theorem algebra_24569 :
    let S := Ioi (-1)
    S.restrict '' {f : ℝ → ℝ | MapsTo f S S ∧
      (∀ x ∈ S, ∀ y ∈ S, f (x + f y + x * f y) = y + f x + y * f x) ∧
      StrictMonoOn (fun x => f x / x) (Ioo (-1) 0) ∧
      StrictMonoOn (fun x => f x / x) (Ioi 0)} =
    S.restrict '' {fun x => -x / (1 + x)} := by
  intro S
  ext f'
  simp only [mem_image, mem_setOf_eq, image_singleton, mem_singleton_iff]
  -- After some simplifications of the goal, we starts the main proof.
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨f, ⟨map, eq, mono₁, mono₂⟩, eq'⟩
    rw [←eq', restrict_eq_restrict_iff]
    intro x hx
    clear f' eq'
    have fix_implies_zero {u : ℝ} (hu : u ∈ S) (fix : f u = u) : u = 0 := by
        -- Putting $x=y=u$ in the given functional equation yields $f\left(u^{2}+2 u\right)=u^{2}+2 u$.
      specialize eq u hu u hu
      rw [fix] at eq
      ring_nf at eq
      simp only [S, mem_Ioi] at hu
      by_contra ne_zero
      by_cases h : u ≤ 0
      · -- Suppose that for $u \in(-1,0)$, $f(u)=u$.
        -- Firstly, we prove that `u ∈ (-1, 0)`.
        have fix₁ : u ∈ Ioo (-1) 0 := by
          simpa using ⟨by linarith, lt_of_le_of_ne h ne_zero⟩
        -- Secondly, we prove that `u ^ 2 + 2u ∈ (-1, 0)`.
        have fix₂ : u * 2 + u ^ 2 ∈ Ioo (-1) 0 := by
          simp only [show u * 2 + u ^ 2 = u * (u + 2) by ring, mem_Ioo]
          constructor
          · rw [← sub_lt_zero]
            convert_to -(1 + u) ^ 2 < 0
            · ring
            · simp only [Left.neg_neg_iff]
              apply sq_pos_of_ne_zero
              linarith
          · simp only [mem_Ioo] at fix₁
            exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
        -- The last condition implies that $f(x)=x$ has at most one solution in $(-1,0)$.
        have fix_unique {u v : ℝ} (hu : u ∈ Ioo (-1) 0) (hv : v ∈ Ioo (-1) 0)
            (u_fix : f u = u) (v_fix : f v = v) : u = v := by
          have := mono₁.eq_iff_eq hu hv
          simp only [mem_Ioo] at hu hv
          rw [← this, u_fix, v_fix, div_self (a := u) (by linarith), div_self (by linarith)]
        specialize fix_unique fix₁ fix₂ fix eq
        -- Since $u \in(-1,0) \Rightarrow u^{2}+2 u \in(-1,0)$, we deduce that $u^{2}+2 u=u$, i.e., $u=-1$ or $u=0$, which is impossible.
        have : u * (u + 1) = 0 := by
          rw [eq_comm, ← sub_eq_zero] at fix_unique
          ring_nf at fix_unique ⊢
          assumption
        simp only [mul_eq_zero] at this
        simp only [mem_Ioo] at fix₁
        cases this <;> linarith
      · -- Similarly, if $f(v)=v$ for $v \in(0, \infty)$, we are led to the same contradiction.
        simp only [not_le] at h
        have fix₁ : u ∈ Ioi 0 := by simpa
        have fix₂ : u * 2 + u ^ 2 ∈ Ioi 0 := by
          simp only [show u * 2 + u ^ 2 = u * (u + 2) by ring, mem_Ioi]
          exact mul_pos h (by linarith)
        -- The last condition implies that $f(x)=x$ has at most one solution in $(0, \infty)$.
        have fix_unique {u v : ℝ} (hu : u ∈ Ioi 0) (hv : v ∈ Ioi 0)
            (u_fix : f u = u) (v_fix : f v = v) : u = v := by
          have := mono₂.eq_iff_eq hu hv
          simp only [mem_Ioi] at hu hv
          rw [← this, u_fix, v_fix, div_self (a := u) (by linarith), div_self (by linarith)]
        -- Similar to the first case, we prove that `u = u ^ 2 + 2u` from the uniqueness of the fixed point of `f` on `(0, +∞)`.
        specialize fix_unique fix₁ fix₂ fix eq
        have : u * (u + 1) = 0 := by
          rw [eq_comm, ← sub_eq_zero] at fix_unique
          ring_nf at fix_unique ⊢
          assumption
        simp only [mul_eq_zero] at this
        cases this <;> linarith
    -- However, for all $x \in S, f(x+(1+x) f(x))=x+(1+x) f(x)$, so we must have $x+(1+x) f(x)=0$.
    specialize eq x hx x hx
    have : x + f x + x * f x ∈ S := by
      simp only [mem_Ioi, S]
      rw [neg_lt_iff_pos_add']
      convert_to 0 < (1 + x) * (1 + f x)
      · ring
      · have hfx := map hx
        simp only [mem_Ioi, neg_lt_iff_pos_add', S] at hx hfx
        exact mul_pos hx hfx
    -- Therefore $f(x)=-\frac{x}{1+x}$ for all $x \in S$.
    specialize fix_implies_zero this eq
    have : 1 + x ≠ 0 := by simp [S] at hx; linarith
    field_simp
    rw [← sub_eq_zero, ← fix_implies_zero]
    ring
  · -- It is directly verified that the function `f(x) = -x / (1+x)` satisfies all the conditions.
    simp only [h, neg_add_rev]
    clear f' h
    refine ⟨_, ⟨?_, ?_, ?_, ?_⟩, rfl⟩
    · -- verify that `f(x)` maps `S` to `S`.
      intro x hx
      simp only [mem_Ioi, S] at hx ⊢
      rw [lt_div_iff (by linarith)]
      linarith
    · -- verify that `f(x)` satisfies the functional equation.
      intro x hx y hy
      simp only [mem_Ioi, S] at hx hy
      have : 1 + x ≠ 0 := by linarith
      have : 1 + y ≠ 0 := by linarith
      field_simp
      ring_nf
      field_simp
      ring
    · -- verify the condition that `f(x) / x` is strictly increasing on `(-1, 0)`.
      intro x hx y hy lt
      simp only [mem_Ioo, S] at hx hy ⊢
      have f_div_x_eq {a : ℝ} (ha : -1 < a ∧ a < 0) : -a / (1 + a) / a = -1 / (1 + a) := by
        have : a ≠ 0 := by linarith
        have : 1 + a ≠ 0 := by linarith
        field_simp
        ring
      rw [f_div_x_eq hx, f_div_x_eq hy, neg_div, neg_div]
      simp only [one_div, neg_lt_neg_iff, gt_iff_lt]
      rw [inv_lt_inv (by linarith) (by linarith)]
      linarith
    · -- verify the condition that `f(x) / x` is strictly increasing on `(0, +∞)`.
      intro x hx y hy lt
      simp only [mem_Ioi, S] at hx hy ⊢
      have f_div_x_eq {a : ℝ} (ha : 0 < a) : -a / (1 + a) / a = -1 / (1 + a) := by
        have : a ≠ 0 := by linarith
        have : 1 + a ≠ 0 := by linarith
        field_simp
        ring
      rw [f_div_x_eq hx, f_div_x_eq hy, neg_div, neg_div]
      simp only [one_div, neg_lt_neg_iff, gt_iff_lt]
      rw [inv_lt_inv (by linarith) (by linarith)]
      linarith
