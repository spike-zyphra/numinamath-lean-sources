import Mathlib
open scoped BigOperators

/- 7. Prove that $\left(1+x+x^{2}+\ldots+x^{100}\right)\left(1+x^{102}\right)-102 x^{101} \geqslant$ $\geqslant 0$. -/
theorem inequalities_205702 {x : ℚ} :
  (∑ i in Finset.range 102, x^(2 * i)) - 102 * x^101 ≥ 0 := by
  -- Split up the sum into two halves
  have union : Finset.range 102 = Finset.range 51 ∪ Finset.Ico 51 102
  · ext i
    apply Iff.intro
    · intro hi
      simp at hi ⊢
      if hi' : i < 51 then left; exact hi';
      else right; exact ⟨Nat.le_of_not_lt hi', hi⟩
    · intro hi
      simp at hi ⊢
      cases hi <;> linarith
  -- Show these halves are disjoint
  have disj : Disjoint (Finset.range 51) (Finset.Ico 51 102) := Finset.disjoint_iff_inter_eq_empty.mpr rfl
  -- Show we can reindex the second sum
  have reorder : ∀ (f : ℕ → ℚ), ∑ i in Finset.Ico 51 102, f i = ∑ i in Finset.range 51, f (101 - i)
  · intro f
    apply Finset.sum_bij (fun i hi ↦ 101 - i)
    · intro a ha
      simp at ha ⊢
      rcases ha with ⟨ha, ha'⟩
      calc
        101 - a ≤ 101 - 51 := Nat.sub_le_sub_left ha 101
        _ < 51 := by norm_num
    · intro a ha b hb hb'
      simp at ha hb
      have ha' : a ≤ 101 := by linarith
      exact tsub_inj_right ha' (by linarith) hb'
    · intro b hb
      use 101 - b
      simp at hb ⊢
      have ineq1 : 51 ≤ 101 - b := by calc
        101 - b ≥ 101 - 50 := by exact Nat.sub_le_sub_left (by linarith) 101
              _ = 51 := by norm_num
      exact ⟨⟨ineq1, Nat.sub_lt_succ 101 b⟩, Nat.sub_sub_self (by linarith)⟩
    · intro a ha
      congr 1
      simp at ha
      exact (Nat.sub_sub_self (by linarith)).symm

  -- Apply the lemmas above:
  calc
    ∑ i in Finset.range 102, x^(2 * i) - 102 * x^101
    -- split up the sum into two halves
    _ = ∑ i in Finset.range 51, x^(2 * i) + ∑ i in Finset.Ico 51 102, x^(2 * i) - 102 * x^101 := by congr 1; rw [union]; apply Finset.sum_union disj
    -- reindex the second sum
    _ = ∑ i in Finset.range 51, (x^(2 * i) + x^(2 * (101 - i))) - 102 * x^101 := by rw [reorder, Finset.sum_add_distrib]
    _ = ∑ i in Finset.range 51, (x^(2 * i) + x^(2 * (101 - i))) - 51 * (2 * x^101) := by ring
    _ = ∑ i in Finset.range 51, (x^(2 * i) + x^(2 * (101 - i)) - 2 * x^101) := by simp
    -- rewrite the summand as a square
    _ = ∑ i in Finset.range 51, (x^i - x^(101 - i))^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp at hi
      rw [sub_sq, ←pow_mul, ←pow_mul, mul_assoc 2 _, ←pow_add, ←Nat.add_sub_assoc (by linarith), Nat.add_sub_self_left]
      ring
    -- a sum of squared terms is nonnegative
    _ ≥ 0 := by apply Finset.sum_nonneg; intro i hi; exact sq_nonneg _