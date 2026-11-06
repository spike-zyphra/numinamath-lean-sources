import Mathlib

open Polynomial

/-2. Let $a, b$, and $c$ be positive real numbers. Determine the largest total number of real roots that the following three polynomials may have among them: $a x^{2}+b x+c, b x^{2}+c x+a$, and $c x^{2}+a x+b$.-/
theorem algebra_158983 : IsGreatest {n : ℕ | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ n =
    {x : ℝ | a * x ^ 2 + b * x + c = 0 ∨ b * x ^ 2 + c * x + a = 0 ∨
    c * x ^ 2 + a * x + b = 0}.ncard} 4 := by
-- Prove an auxillary lemma that quadratic polynomial with positive coefficients has at most two roots
  have aux : ∀ p q r : ℝ, 0 < p → 0 < q → 0 < r → {x | p * x ^ 2 + q * x + r = 0}.ncard ≤ 2 := by
    intro p q r ppos qpos rpos
    suffices : {x | p * x ^ 2 + q * x + r = 0} ⊆ (C p * X ^ 2 + C q * X + C r).roots.toFinset
    · apply Set.ncard_le_ncard at this; simp at this
      calc
        _ ≤ _ := this
        _ ≤ (C p * X ^ 2 + C q * X + C r).roots.card := by
          apply Multiset.toFinset_card_le
        _ ≤ (C p * X ^ 2 + C q * X + C r).natDegree := by apply card_roots'
        _ ≤ _ := by compute_degree
    simp [Set.subset_def]; intros; constructor
    · intro h; simp [ext_iff] at h
      specialize h 0; simp at h; linarith
    assumption
-- Splite the goal to two subgoals
  simp [IsGreatest, upperBounds]; constructor
  -- Use $(a, b, c)=(1, 5, 6)$ to fulfill the goal
  · use 1; norm_num; use 5; norm_num
    use 6; norm_num
  -- Prove the set of solutions of the equations in question is ${-2, -3, -1, -1/5}$
    suffices : {x : ℝ | x ^ 2 + 5 * x + 6 = 0 ∨ 5 * x ^ 2 + 6 * x + 1 = 0 ∨
    6 * x ^ 2 + x + 5 = 0} = {-2, -3, -1, -1/5}
    · rw [this]; repeat rw [Set.ncard_insert_of_not_mem]
      all_goals simp
      all_goals linarith
    simp [Set.ext_iff]; intro x; constructor
    · intro h; rcases h with h|h|h
      · simp [show x ^ 2 + 5 * x + 6 = (x + 2) * (x + 3) by ring] at h
        rcases h with h|h
        all_goals rw [← eq_neg_iff_add_eq_zero] at h; simp [h]
      · simp [show 5 * x ^ 2 + 6 * x + 1 = (5 * x + 1) * (x + 1) by ring] at h
        rcases h with h|h
        · replace h : x = -1 / 5 := by linarith
          simp [h]
        rw [← eq_neg_iff_add_eq_zero] at h; simp [h]
      rw [show 6 * x ^ 2 + x + 5 = 6 * (x + 1 / 12) ^ 2 + 119 / 24 by ring] at h
      have : 0 ≤ 6 * (x + 1 / 12) ^ 2 := by positivity
      linarith only [this, h]
    intro h; rcases h with h|h|h|h
    all_goals norm_num [h]
-- To prove the upper bound goal, we first introduce variables and assumptions
  intro n a apos b bpos c cpos hn; rw [hn]; clear n hn
  rw [← Set.sep_univ, Set.sep_or, Set.sep_or]; simp
-- Assume the contrary that the cardinality is greater than $4$, then all the three solution sets have to be nonempty
  by_contra! h; replace this : {x | a * x ^ 2 + b * x + c = 0}.Nonempty ∧ 
  {x | b * x ^ 2 + c * x + a = 0}.Nonempty ∧ {x | c * x ^ 2 + a * x + b = 0}.Nonempty := by
    by_contra!; by_cases h' : {x | a * x ^ 2 + b * x + c = 0} = ∅
    · simp [h'] at h; suffices : ({x | b * x ^ 2 + c * x + a = 0} ∪
      {x | c * x ^ 2 + a * x + b = 0}).ncard ≤ 4
      · linarith only [this, h]
      calc
        _ ≤ _ := Set.ncard_union_le {x | b * x ^ 2 + c * x + a = 0} {x | c * x ^ 2 + a * x + b = 0}
        _ ≤ 2 + 2 := by
          gcongr; all_goals apply aux
          all_goals assumption
        _ = _ := by simp
    by_cases h'' : {x | b * x ^ 2 + c * x + a = 0} = ∅
    · simp [h''] at h; suffices : ({x | a * x ^ 2 + b * x + c = 0} ∪
      {x | c * x ^ 2 + a * x + b = 0}).ncard ≤ 4
      · linarith only [this, h]
      calc
        _ ≤ _ := Set.ncard_union_le {x | a * x ^ 2 + b * x + c = 0} {x | c * x ^ 2 + a * x + b = 0}
        _ ≤ 2 + 2 := by
          gcongr; all_goals apply aux
          all_goals assumption
        _ = _ := by simp
    specialize this (Set.nonempty_iff_ne_empty.mpr h') (Set.nonempty_iff_ne_empty.mpr h'')
    simp [this] at h; suffices : ({x | a * x ^ 2 + b * x + c = 0} ∪
    {x | b * x ^ 2 + c * x + a = 0}).ncard ≤ 4
    · linarith only [this, h]
    calc
      _ ≤ _ := Set.ncard_union_le {x | a * x ^ 2 + b * x + c = 0} {x | b * x ^ 2 + c * x + a = 0}
      _ ≤ 2 + 2 := by
        gcongr; all_goals apply aux
        all_goals assumption
      _ = _ := by simp
-- Choose a solution to each of the three equations and derive a contradiciton from the positivity of their discriminants
  rcases this with ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩
  simp at hx hy hz
  replace hx : (2 * a * x + b) ^ 2 = b ^ 2 - 4 * a * c := by
    rw [← sub_eq_zero]; ring_nf; calc
      _ = 4 * a * (a * x ^ 2 + b * x + c) := by ring
      _ = _ := by rw [hx]; simp
  replace hy : (2 * b * y + c) ^ 2 = c ^ 2 - 4 * a * b := by
    rw [← sub_eq_zero]; ring_nf; calc
      _ = 4 * b * (b * y ^ 2 + c * y + a) := by ring
      _ = _ := by rw [hy]; simp
  replace hz : (2 * c * z + a) ^ 2 = a ^ 2 - 4 * b * c := by
    rw [← sub_eq_zero]; ring_nf; calc
      _ = 4 * c * (c * z ^ 2 + a * z + b) := by ring
      _ = _ := by rw [hz]; simp
  suffices : 64 * (a * b * c) ^ 2 ≤ (a * b * c) ^ 2
  · replace this : (a * b * c) ^ 2 ≤ 0 := by linarith only [this]
    convert this; simp
    positivity
  calc
    _ = (4 * a * c) * (4 * a * b) * (4 * b * c) := by ring
    _ ≤ b ^ 2 * c ^ 2 * a ^ 2 := by
      gcongr; rw [← sub_nonneg, ← hx]; positivity
      rw [← sub_nonneg, ← hy]; positivity
      rw [← sub_nonneg, ← hz]; positivity
    _ = _ := by ring
  