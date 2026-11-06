import Mathlib
open Nat

set_option linter.unusedVariables false

/- Soit $n \geqslant 2$ un entier. Anna a écrit au tableau $n$ entiers $a_{1}, a_{2}, \ldots, a_{n}$ deux à deux distincts. Elle remarque alors que, quelle que soit la manière de sélectionner $n-1$ de ces entiers, leur somme est divisible par $n$.
Démontrer que la somme de l'ensemble des $n$ entiers est divisible par $n$. -/
theorem number_theory_605578 (n : ℕ) (hn : 2 ≤ n) (a : Fin n → ℤ)
    (ha : ∀ i j, i ≠ j → a i ≠ a j)
    (h : ∀ s : Finset (Fin n), s.card = n - 1 → ∑ i ∈ s, a i ≡ 0 [ZMOD n]) :
    ∑ i : Fin n, a i ≡ 0 [ZMOD n] := by
    -- Define $s$ as the sum of all $n$ integers.
  let s : ℤ := ∑ i : Fin n, a i
  have h_s_def : s = ∑ i : Fin n, a i := by
    rfl
  -- Select the sum of $n-1$ integers as $s - a i$.
  have h_sum_minus : ∀ i : Fin n, ∃ t : Finset (Fin n), t.card = n - 1 ∧ ∑ j ∈ t, a j = s - a i := by
    intro i
    let t := Finset.univ.erase i
    use t
    constructor
    · rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
      simp only [Fintype.card_fin]
    · have h_erase_sum : ∑ j ∈ Finset.univ.erase i, a j = ∑ j ∈ Finset.univ, a j - a i := by
        exact Finset.sum_erase_eq_sub (Finset.mem_univ i)
      rw [← h_s_def] at h_erase_sum
      exact h_erase_sum
  -- From the condition, $s - a i ≡ 0 [ZMOD n]$, i.e., $a i ≡ s [ZMOD n]$.
  have h_a_eq_s : ∀ i : Fin n, a i ≡ s [ZMOD n] := by
    intro i
    obtain ⟨s', hs'_card, hs'_sum⟩ := h_sum_minus i
    have h_s' : ∑ j ∈ s', a j ≡ 0 [ZMOD n] := h s' hs'_card
    rw [hs'_sum] at h_s'
    have h_s_ai : s - a i ≡ 0 [ZMOD n] := h_s'
    have h_ai_s : s ≡ a i [ZMOD n] := by
      rw [Int.ModEq] at h_s' ⊢
      simp_all [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    exact Int.ModEq.symm h_ai_s
  -- All a i are congruent to $s$ modulo $n$.
  have h_all_eq : ∀ i j : Fin n, a i ≡ a j [ZMOD n] := by
    intro i j
    exact Int.ModEq.trans (h_a_eq_s i) (Int.ModEq.symm (h_a_eq_s j))
  -- The total sum $s ≡ n s ≡ 0 [ZMOD n]$.
  have h_s_zero : s ≡ 0 [ZMOD n] := by
    have h_sum_n_s : s ≡ n • s [ZMOD n] := by
      have h_each_a_eq_s : ∀ i : Fin n, a i ≡ s [ZMOD n] := by
        intro i
        apply h_a_eq_s
      have h_sum_eq_sum_s : ∑ i : Fin n, a i ≡ ∑ i : Fin n, s [ZMOD n] := by
        apply Finset.sum_hom_rel
        · exact Int.ModEq.refl 0
        · intro i b c h_bc
          exact Int.ModEq.add (h_each_a_eq_s i) h_bc
      have h_sum_s_eq_ns : ∑ i : Fin n, s = n • s := by
        simp [Finset.sum_const, nsmul_eq_mul]
      -- Replace $∑ a_i$ with $s$ and $∑ s$ with $n • s$ in the congruence relation.
      rw [h_s_def] at h_sum_eq_sum_s
      rw [h_sum_s_eq_ns] at h_sum_eq_sum_s
      -- Finally obtain $s ≡ n • s [ZMOD n]$.
      exact h_sum_eq_sum_s
    have h_n_s_zero : n • s ≡ 0 [ZMOD n] := by
      rw [nsmul_eq_mul]
      simp [Int.mul_emod, Int.ModEq]
    exact Int.ModEq.trans h_sum_n_s h_n_s_zero
  exact h_s_zero