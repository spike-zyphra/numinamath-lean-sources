import Mathlib

open Finset Real

theorem Combinatorics_c2 {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = 2 * n) :
    ∀ r ∈ Set.Icc (0:ℝ) (2 * n - 2), ∃ t : Finset (Fin n), r ≤ ∑ i ∈ t, a i ∧ ∑ i ∈ t, a i ≤ r + 2 :=
by
  -- `valid` defines our more general statement for the induction hypothesis, i.e.:
  -- Suppose that you have `n` blocks, each of weight at least 1, and of total weight `s ≤ 2n`. Then for every `r` with `-2 ≤ r ≤ s`, 
  -- you can choose some of the blocks whose total weight is at least `r` but at most `r+2`.
  let valid {n : ℕ} (a : Fin (n + 1) → ℝ) (s : ℝ) := ∀ r ∈ Set.Icc (-2) s, ∃ t : Finset (Fin (n + 1)), r ≤ ∑ i ∈ t, a i ∧ ∑ i ∈ t, a i ≤ r + 2
  have temp₁ {n : ℕ} (a : Fin (n + 1) → ℝ) (s : ℝ) (ha : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = s) (hle : s ≤ 2 * (n + 1)) :
    valid a s :=
  by
    -- We proceed by induction.
    induction n generalizing s with
    | zero =>
      -- The base case `n=1` is trivial.
      rintro r ⟨hr, hs⟩
      simp only [Nat.reduceAdd, univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton, CharP.cast_eq_zero, zero_add, mul_one] at *
      by_cases h : r ≤ 0
      · refine ⟨∅, ?_⟩; simp_all only [sum_empty, true_and]; linarith
      · refine ⟨{0}, ?_⟩; simp_all only [not_le, sum_singleton, true_and]; linarith
    | succ n ih =>
      -- Note that we have shifted to `n + 2` instead of `n` from the written solution.
      -- Let `i` be the index of the block with maximum weight.
      -- To formalize the idea of removing this largest weight and doing induction on the rest of the blocks,
      -- it's easiest to first rearrange our weights such that the largest is in the last position.
      -- Thus `a'` is the rearrangement, and then `a_init` are weights with the largest removed.
      have ⟨i, hi, heqi⟩ := Finset.exists_mem_eq_sup' ⟨0, mem_univ 0⟩ a
      let a' := a ∘ (Equiv.swap i ⟨n.succ, by omega⟩).toEmbedding
      let a_init := Fin.init a'
      have h₀ : ∀ j : Fin (n + 1), a_init j = a' (Fin.castLE (Nat.le_succ (n + 1)) j) := fun j ↦ by
        simp only [Fin.init, Function.comp_apply, Equiv.swap_apply_def, Fin.castLE, a_init, a']; congr
      -- We first prove that the rearranged weights are valid using the induction hypothesis.
      have h₁ : valid a' s := by
        have hsum' : ∑ i : Fin (n + 1 + 1), a' i = s := by simpa [a', Equiv.sum_comp]
        have heqi' : univ.sup' ⟨0, mem_univ _⟩ a' = a' ⟨n.succ, by omega⟩ := by
          rw [sup'_comp_eq_map a ⟨0, mem_univ _⟩]
          simpa [a']
        have part₀ : ∀ (i : Fin (n + 1)), 1 ≤ a_init i := fun i ↦ by
          simp only [Fin.init, Function.comp_apply, a_init, a']; exact ha _
        have part₁ : ∑ i : Fin (n + 1), a_init i = s - a' ⟨n.succ, by omega⟩ := by
          rw [← hsum', Fin.sum_univ_castSucc a', Fin.last, add_sub_cancel_right]; congr
        -- Let `x = a' (n + 1)`.
        -- Clearly `x ≥ s / (n + 2)`, so `s - x ≤ (n + 1) / (n + 2) * x ≤ 2(n + 1)`.
        have part₂ : s - a' ⟨n.succ, by omega⟩ ≤ 2 * (n + 1) := by
          have : s / (n + 1 + 1) ≤ a' ⟨n.succ, by omega⟩ := by
            by_contra!; revert hsum'; refine ne_of_lt ?_
            calc ∑ i : Fin (n + 1 + 1), a' i
              _ < ∑ i : Fin (n + 1 + 1), s / (n + 1 + 1) := by
                exact sum_lt_sum_of_nonempty ⟨0, mem_univ _⟩ fun i _ ↦ lt_of_le_of_lt (heqi' ▸ Finset.le_sup' a' (mem_univ _)) this
              _ = s := by field_simp
          calc s - a' ⟨n.succ, by omega⟩
            _ ≤ s - s / (n + 1 + 1) := by linarith
            _ = (n + 1 + 1) * s / (n + 1 + 1) - s / (n + 1 + 1) := by field_simp
            _ = (n + 1) * s / (n + 1 + 1) := by rw [← sub_div, add_mul, one_mul, add_sub_cancel_right]
            _ = s / (n + 1 + 1) * (n + 1) := by rw [mul_div_assoc, mul_comm]
            _ ≤ 2 * (↑n + 1) := by
              rw [Nat.cast_add, Nat.cast_one] at hle
              rwa [mul_le_mul_right (by linarith), div_le_iff₀ (by linarith)]
        -- Hence, if we exclude a block `x`, we can apply the inductive hypothesis...
        have ih := ih a_init (s - a' ⟨n.succ, by omega⟩) part₀ part₁ part₂
        intro r hr
        by_cases h : r ≤ s - a' ⟨n.succ, by omega⟩
        · -- ... to show that the claim holds for any `-2 ≤ r ≤ s - x`.
          have ⟨t, ht⟩ := ih r ⟨hr.1, h⟩
          exact ⟨t.map (Fin.castLEEmb (Nat.le_succ _)), by simpa [sum_map, Fin.castLEEmb_apply]⟩
        · -- To cover the rest of the interval, we need to show that `x - 2 ≤ s - x`.
          have h₃ : r - a' ⟨n.succ, by omega⟩ ∈ Set.Icc (-2) (s - a' ⟨n.succ, by omega⟩) := by
            simp only [Nat.succ_eq_add_one, Set.mem_Icc, sub_nonneg, tsub_le_iff_right, sub_add_cancel]
            simp only [Nat.succ_eq_add_one, not_le] at h
            refine ⟨le_sub_iff_add_le.2 (le_trans ?_ (le_of_lt h)), hr.2⟩
            -- Each block weight is at least 1, so we have `x ≤ s - (n + 1)`.
            have h₅ : a' ⟨n.succ, by omega⟩ ≤ s - n.succ := by
              have h₆ : (n.succ : ℝ) = ∑ x ∈ (univ : Finset (Fin (n + 1 + 1))).erase ⟨n.succ, by omega⟩, 1 := by simp
              rw [← @insert_erase (Fin (n + 1 + 1)) _ univ ⟨n.succ, by omega⟩ (mem_univ _), sum_insert (not_mem_erase _ _)] at hsum'
              rw [le_sub_iff_add_le, ← hsum', add_le_add_iff_left, h₆]
              refine sum_le_sum fun i _ ↦ by simp [a']; exact ha _
            -- So we have `x - 2 ≤ (s - (n + 1)) - 2 = s - (2(n + 2) - (n + 1)) ≤ s - (s - (n + 1)) ≤ s - x`.
            calc -2 + a' ⟨n.succ, by omega⟩
              _ ≤ -2 + s - n.succ := by linarith
              _ = -2 + s - (2 * (n + 1) - n.succ) := by simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]; ring
              _ ≤ s - (s - n.succ) := by simp only [Nat.cast_add, Nat.cast_one] at hle; linarith
              _ ≤ s - a' ⟨n.succ, by omega⟩ := by simp only [sub_le_sub_iff, add_le_add_iff_left]; assumption
          have ⟨t, ht⟩ := ih (r - a' ⟨n.succ, by omega⟩) h₃
          -- Adding the excluded block to each of those combinations, we see that the claim holds when `s - x ≤ r ≤ s`.
          have h₄ : ⟨n.succ, by omega⟩ ∉ (t.map (Fin.castLEEmb (Nat.le_succ _))) := by
            simp only [Nat.succ_eq_add_one, mem_map, Fin.castLEEmb_apply, Fin.castLE, Fin.mk.injEq, not_exists, not_and]
            exact fun x _ ↦ ne_of_lt x.2
          refine ⟨insert ⟨n.succ, by omega⟩ (t.map (Fin.castLEEmb (Nat.le_succ _))), ?_⟩
          simp only [Nat.succ_eq_add_one, sum_insert h₄, sum_map, Fin.castLEEmb_apply, ← h₀]
          refine ⟨sub_le_iff_le_add'.1 ht.1, ?_⟩
          rw [add_comm_sub, ← add_sub_assoc, le_sub_iff_add_le, add_comm _ (a' ⟨n.succ, _⟩)] at ht
          exact ht.2
      -- Finally, we rearrange back to the original weights...
      intro r hr
      have ⟨t, ht⟩ := h₁ r hr
      refine ⟨t.map $ Equiv.swap i ⟨n.succ, by omega⟩, ?_⟩
      simp [sum_map, Equiv.coe_toEmbedding]
      simp [Function.comp_apply, a'] at ht
      exact ht
  -- and then specialize our general statement, to complete the proof.
  cases n with
  | zero => contradiction
  | succ n =>
    intro r hr
    rw [Nat.cast_add, Nat.cast_one] at hsum hr
    refine temp₁ a (2 * (n + 1)) ha hsum le_rfl r
      (Set.mem_of_subset_of_mem (Set.Icc_subset_Icc (by simp) (by simp)) hr)
