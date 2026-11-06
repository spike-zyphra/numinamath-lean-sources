import Mathlib

/- Given 7 distinct strictly positive integers whose sum is 100, show that one can choose three of them whose sum is greater than or equal to 50. -/
theorem number_theory_99160 (s : Finset ℕ) (H₀ : s.card = 7) (H₁ : ∑ i ∈ s, i = 100) (H₂ : ∀ i ∈ s, i > 0) :
    ∃ t ⊆ s, t.card = 3 ∧ ∑ i ∈ t, i ≥ 50 := by
  -- We first sort the elements of s.
  let l := s.sort (· ≤ ·)
  -- We then prove that l is a list of 7 distinct positive integers that is strictly increasing.
  have hl₁ : l.length = 7 := by simp [l, H₀]
  have hl₂ : l.Nodup := Finset.sort_nodup _ _
  have hl₃ : l.Sorted (· < ·) := (Finset.sort_sorted _ _).lt_of_le hl₂
  -- So 0 < l[0] < l[1] < l[2] < l[3] < l[4] < l[5] < l[6].
  have h₀ : 0 < l[0] := by
    refine H₂ l[0] ?_
    simp [l, ← Finset.mem_sort (· ≤ ·)]
  have h₁ : l[0] < l[1] := List.Sorted.rel_get_of_lt hl₃ (by simp)
  have h₂ : l[1] < l[2] := List.Sorted.rel_get_of_lt hl₃ (by simp)
  have h₃ : l[2] < l[3] := List.Sorted.rel_get_of_lt hl₃ (by simp)
  have h₄ : l[3] < l[4] := List.Sorted.rel_get_of_lt hl₃ (by simp)
  have h₅ : l[4] < l[5] := List.Sorted.rel_get_of_lt hl₃ (by simp)
  have h₆ : l[5] < l[6] := List.Sorted.rel_get_of_lt hl₃ (by simp)
  -- We have l[0] + l[1] + l[2] + l[3] + l[4] + l[5] + l[6] = 100.
  have h₇ : l[0] + l[1] + l[2] + l[3] + l[4] + l[5] + l[6] = 100 := by
    convert (List.sum_toFinset id hl₂).symm
    . have h₇ : ∑ i : Fin l.length, l[i] = ∑ i : Fin 7, l[i] := (Fin.sum_congr' l.get hl₁.symm).symm
      simp [← Fin.sum_univ_get, ← Fin.getElem_fin, h₇]
      simp [Finset.sum]
      ac_rfl
    . simp [l, Finset.sort_toFinset, H₁]
  -- We then prove that l[4], l[5], l[6] are distinct.
  have htm : ({l[4], l[5], l[6]} : Multiset ℕ).Nodup := by
    simp
    refine ⟨⟨?_, ?_⟩, ?_⟩
    all_goals linarith
  -- We set t to be {l[4], l[5], l[6]}.
  use ⟨{l[4], l[5], l[6]}, htm⟩
  refine ⟨?_, rfl, ?_⟩
  . simp [Finset.subset_iff]
    simp [l, ← Finset.mem_sort (· ≤ ·)]
  . simp [Finset.sum]
    -- If the conclusion is false, then l[4] ≤ 15
    by_contra! H
    have h₈ : l[4] ≤ 15 := by
      -- Otherwise, we have l[4] ≥ 16, l[5] ≥ 17, l[6] ≥ 18.
      by_contra! h₈
      have h₉ : l[5] ≥ 17 := by linarith
      have h₁₀ : l[6] ≥ 18 := by linarith
      linarith
    -- But now we have l[3] ≤ 14, l[2] ≤ 13, l[1] ≤ 12, l[0] ≤ 11.
    -- We get l[0] + l[1] + l[2] + l[3] ≤ 50
    -- So l[4] + l[5] + l[6] ≥ 50 again
    have h₉ : l[3] ≤ 14 := by linarith
    have h₁₁ : l[2] ≤ 13 := by linarith
    have h₁₂ : l[1] ≤ 12 := by linarith
    have h₁₃ : l[0] ≤ 11 := by linarith
    linarith
