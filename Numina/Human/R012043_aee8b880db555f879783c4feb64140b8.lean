import Mathlib

open Finset

/- 4. If any $n$ integers are taken, it is always possible to select three numbers whose sum is divisible by 3. Then the minimum value of $n$ is ( ).
(A) 2
(B) 3
(C) 4
(D) 5 -/
theorem number_theory_325554 :
    IsLeast {n : ℕ | n ≥ 3 ∧ ∀ S : Finset ℤ, #S = n → ∃ T ⊆ S, #T = 3 ∧ 3 ∣ T.sum id} 5 := by
  constructor
  . -- We show that any set of 5 integers has a subset of 3 integers whose sum is divisible by 3.
    simp
    intro S hS
    -- We partition S into 3 residue classes modulo 3.
    have hsum := card_eq_sum_card_fiberwise (f := fun (x : ℤ) => (x : ZMod 3)) (s := S) (t := univ) (by simp)
    -- We show that either every residue class has at least one element, or one of the residue classes has at least 3 elements.
    obtain h | h : (∀ i : ZMod 3, 0 < #{x ∈ S | (x : ℤ) = i}) ∨ ∃ i : ZMod 3, 3 ≤ #{x ∈ S | (x : ℤ) = i} := by
      -- Expand the sum.
      simp only [Finset.sum, univ, Fintype.elems, List.finRange] at hsum
      simp at hsum
      -- Eliminate the `∀` and `∃` in the goal.
      suffices h : 0 < #{x ∈ S | (x : ℤ) = (0 : ZMod 3)} ∧ 0 < #{x ∈ S | (x : ℤ) = (1 : ZMod 3)} ∧ 0 < #{x ∈ S | (x : ℤ) = (2 : ZMod 3)} ∨ (3 ≤ #{x ∈ S | (x : ℤ) = (0 : ZMod 3)} ∨ 3 ≤ #{x ∈ S | (x : ℤ) = (1 : ZMod 3)} ∨ 3 ≤ #{x ∈ S | (x : ℤ) = (2 : ZMod 3)}) by
        rcases h with ⟨h₁, h₂, h₃⟩ | h | h | h
        . refine Or.inl fun i => ?_
          fin_cases i
          . simp [h₁]
          . simp [h₂]
          . simp [h₃]
        . right
          use 0
        . right
          use 1
        . right
          use 2
      -- Now the goal is purely arithmetic.
      omega
    . -- If 1 holds, then each residue class has at least one element.
      simp at h
      -- We take one element from each residue class.
      obtain ⟨x₀, h₀⟩ := h 0
      obtain ⟨x₁, h₁⟩ := h 1
      obtain ⟨x₂, h₂⟩ := h 2
      simp at h₀ h₁ h₂
      rcases h₀ with ⟨hx₀, h₀⟩
      rcases h₁ with ⟨hx₁, h₁⟩
      rcases h₂ with ⟨hx₂, h₂⟩
      -- We take {x₀, x₁, x₂} as T.
      let T : Finset ℤ := ⟨{x₀, x₁, x₂}, by
        -- x₀, x₁, x₂ are distinct since they have different residues modulo 3.
        -- x₀, x₁, x₂ are distinct since they have different residues modulo 3.
        simp
        refine ⟨⟨?_, ?_⟩, ?_⟩
        all_goals
          intro h
          simp [h, h₀, h₁, h₂] at h₀ h₁ h₂
        . absurd h₀
          decide
        . absurd h₁
          decide
      ⟩
      -- T is a subset of S.
      have hT₁ : T ⊆ S := by
        intro x hx
        simp [T] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      -- T has 3 elements.
      have hT₂ : #T = 3 := by
        simp [Finset.card, T]
      refine ⟨T, hT₁, hT₂, ?_⟩
      -- Since 0 + 1 + 2 = 0 in ZMod 3, the sum of T is divisible by 3.
      simp [T, Finset.sum]
      rw [show (3 : ℤ) = (3 : ℕ) by simp, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp [h₀, h₁, h₂]
      decide
    . rcases h with ⟨i, hcard⟩
      -- We take a subset of [i] with 3 elements as T.
      obtain ⟨T, hT₁, hT₂⟩ := Finset.exists_subset_card_eq hcard
      refine ⟨T, (hT₁.trans (filter_subset _ _)), hT₂, ?_⟩
      -- We write T as {x₀, x₁, x₂}.
      obtain ⟨x₀, x₁, x₂, h₀₁, h₀₂, h₁₂, rfl⟩ := Finset.card_eq_three.mp hT₂
      simp [h₀₁, h₀₂, h₁₂]
      simp [Finset.instHasSubset] at hT₁
      rcases hT₁ with ⟨⟨hx₀, h₀⟩, ⟨hx₁, h₁⟩, ⟨hx₂, h₂⟩⟩
      -- Since i + i + i = 0 in ZMod 3, the sum of T is divisible by 3.
      rw [show (3 : ℤ) = (3 : ℕ) by simp, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp [h₀, h₁, h₂]
      rw [show i + (i + i) = 3 * i by ring, mul_eq_zero]
      left
      decide
  . -- If n < 5, then there exists a set of n integers that does not have a subset of 3 integers whose sum is divisible by 3.
    intro n ⟨hn₁, hn₂⟩
    by_contra! h
    interval_cases n
    . -- If n = 3, we take S = {0, 1, 3}.
      specialize hn₂ (S := {0, 1, 3}) (by simp)
      absurd hn₂
      native_decide
    . -- If n = 4, we take S = {0, 1, 3, 4}.
      specialize hn₂ (S := {0, 1, 3, 4}) (by simp)
      absurd hn₂
      native_decide
