import Mathlib

open Finset Polynomial

/- Lemma: If $S$ is a non-empty finite set of integers, then the number of elements in $S$ is at most $b + 1 - a$, where $a$ and $b$ are the minimum and maximum elements of $S$, respectively. -/
lemma card_le_max_succ_sub_min {S : Finset ℤ} (hS : S.Nonempty) :
    #S ≤ S.max' hS + 1 - S.min' hS := by
  -- $S$ is a subset of the interval between the minimum and maximum elements of $S$
  have H : S ⊆ Finset.Icc (S.min' hS) (S.max' hS) := by
    intro x hx
    simp
    exact ⟨min'_le S x hx, le_max' S x hx⟩
  -- So the number of elements in $S$ is at most the number of elements in the interval between the minimum and maximum elements of $S$
  apply Finset.card_mono at H
  zify at H
  rwa [Int.card_Icc_of_le _ _ (Int.le_add_one (min'_le S (S.max' hS) (max'_mem S hS)))] at H

/- 5. Let $f(x)$ be an integer-coefficient polynomial of degree 1991, and let $g(x)=f^{2}(x)-9$. Prove that the number of distinct integer roots of $g(x)$ cannot exceed 1991. -/
theorem algebra_225597 {f : ℤ[X]} (hf : f.natDegree = 1991) (g : ℤ[X]) (hg : g = f ^ 2 - 9) :
    #g.roots.toFinset ≤ 1991 := by
  -- Assume for contradiction that the number of distinct integer roots of $g(x)$ exceeds 1991
  by_contra! H
  -- Let $S$ be the set of distinct integer roots of $f(x) - 3$
  let S := (f - 3).roots.toFinset
  -- Let $T$ be the set of distinct integer roots of $f(x) + 3$
  let T := (f + 3).roots.toFinset
  -- The degree of $f(x) - 3$ is 1991
  have hS₀ : (f - 3).natDegree = 1991 := by
    rwa [natDegree_sub_eq_left_of_natDegree_lt]
    rw [hf, show 3 = C (3 : ℤ) by simp, natDegree_C]
    simp
  -- $f(x) - 3$ is not the zero polynomial
  have h₁ : f - 3 ≠ 0 := by
    rintro h
    simp [h] at hS₀
  -- The degree of $f(x) + 3$ is 1991
  have hT₀ : (f + 3).natDegree = 1991 := by
    rwa [natDegree_add_eq_left_of_natDegree_lt]
    rw [hf, show 3 = C (3 : ℤ) by simp, natDegree_C]
    simp
  -- $f(x) + 3$ is not the zero polynomial
  have h₂ : f + 3 ≠ 0 := by
    rintro h
    simp [h] at hT₀
  -- $g(x) = (f(x) - 3)(f(x) + 3)$
  replace hg : g = (f - 3) * (f + 3) := by
    rw [hg]
    ring
  -- $g(x)$ is not the zero polynomial
  have h₃ : g ≠ 0 := by
    simp [hg, h₁, h₂]
  -- The number of distinct integer roots of $f(x) - 3$ is at most 1991
  have hS₁ : S.card ≤ 1991 := by
    calc S.card
      _ ≤ (f - 3).roots.card := Multiset.toFinset_card_le _
      _ ≤ (f - 3).natDegree := card_roots' (f - 3)
      _ = 1991 := hS₀
  -- The number of distinct integer roots of $f(x) + 3$ is at most 1991
  have hT₁ : T.card ≤ 1991 := by
    calc T.card
      _ ≤ (f + 3).roots.card := Multiset.toFinset_card_le _
      _ ≤ (f + 3).natDegree := card_roots' (f + 3)
      _ = 1991 := hT₀
  -- $S \cup T$ is the set of distinct integer roots of $g(x)$
  have H₁ : g.roots.toFinset = S ∪ T := by
    ext x
    simp [S, T, h₁, h₂, h₃, hg]
  -- $S$ is non-empty since $T$ has at most 1991 elements, but $S \cup T$ has more than 1991 elements
  have hS₂ : S.Nonempty := by
    by_contra! hSe
    simp at hSe
    simp [H₁, hSe] at H
    exact not_le_of_gt H hT₁
  -- The same argument shows that $T$ is non-empty
  have hT₂ : T.Nonempty := by
    by_contra! hTe
    simp at hTe
    simp [H₁, hTe] at H
    exact not_le_of_gt H hS₁
  -- We have $b_S + 1 - a_S + b_T + 1 - a_T > 1991$
  -- where $a_S$ and $b_S$ are the minimum and maximum elements of $S$, respectively, and $a_T$ and $b_T$ are the minimum and maximum elements of $T$, respectively
  have H₂ : (S.max' hS₂ + 1 - S.min' hS₂) + (T.max' hT₂ + 1 - T.min' hT₂) > 1991 := by
    calc (S.max' hS₂ + 1 - S.min' hS₂) + (T.max' hT₂ + 1 - T.min' hT₂)
      _ ≥ S.card + T.card := add_le_add (card_le_max_succ_sub_min hS₂) (card_le_max_succ_sub_min hT₂) -- Use the lemma
      _ ≥ (S ∪ T).card := by norm_cast; exact card_union_le S T
      _ = #g.roots.toFinset := by rw [H₁]
      _ > 1991 := Int.lt_of_toNat_lt H
  -- We can find $x \in S$ and $y \in T$ such that $6 < |x - y|$
  obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ S, ∃ y ∈ T, 6 < |x - y| := by
    -- If otherwise, we have $6 \leq |x - y|$ for all $x \in S$ and $y \in T$
    by_contra! h₄
    -- Take $x = b_S$ and $y = a_T$
    have h₅ := h₄ (S.max' hS₂) (max'_mem S hS₂) (T.min' hT₂) (min'_mem T hT₂)
    -- Take $x = a_S$ and $y = b_T$
    have h₆ := h₄ (S.min' hS₂) (min'_mem S hS₂) (T.max' hT₂) (max'_mem T hT₂)
    -- We derive a contradiction
    rw [abs_le] at h₅ h₆
    linarith
  -- $x$ and $y$ are roots of $f(x) - 3$ and $f(x) + 3$, respectively
  simp [S, T, h₁, h₂] at hx hy
  -- $x - y$ divides $f(x) - f(y)$
  have h₄ : x - y ∣ f.eval x - f.eval y := sub_dvd_eval_sub x y f
  -- $f(x) - f(y) = 6$
  rw [show f.eval x - f.eval y = 6 by linarith] at h₄
  -- But $6 < |x - y|$
  replace hxy : 6 < (x - y).natAbs := by zify; exact hxy
  -- We get a contradiction
  apply Int.natAbs_le_of_dvd_ne_zero at h₄
  simp at h₄
  exact not_le_of_gt hxy h₄
