import Mathlib

open Finset

/- If we are given $n+1$ distinct integers between 1 and $2 n$, at least two of these integers are coprime. -/
theorem number_theory_149913 (n : ℕ) (hnpos : 0 < n) (S : Finset ℕ) (hS₁ : S.card = n + 1) (hS₂ : S ⊆ Icc 1 (2 * n)) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a.Coprime b := by
  -- We use the Pigeonhole Principle.
  -- Let's group 1, 2; 3, 4; ...; 2n-1, 2n into n groups.
  -- The group i contains the integers {2i-1, 2i}.
  -- So integer x is in the group (x + 1) / 2.
  let f (x : ℕ) := (x + 1) / 2
  -- The groups are labeled from 1 to n.
  have hf : ∀ x ∈ S, f x ∈ Icc 1 n := by
    intro x hx
    simp [f]
    have hx' := hS₂ hx
    simp at hx'
    -- Linear problem in natural numbers.
    omega
  -- Use the Pigeonhole Principle.
  -- There are n+1 integers in S, but only n groups.
  -- So there are at least two integers in S that are in the same group.
  obtain ⟨x, hx, y, hy, h₁, h₂⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to (show (Icc 1 n).card < S.card by simp [hS₁]) hf
  -- x and y are the integers we are looking for.
  refine ⟨x, hx, y, hy, h₁, ?_⟩
  simp [f] at h₂
  -- Since (x + 1) / 2 = (y + 1) / 2, we have x = y + 1 or y = x + 1.
  -- In both cases, x and y are coprime.
  obtain rfl | rfl : x = y + 1 ∨ y = x + 1 := by omega
  . exact Nat.coprime_self_add_left.mpr (Nat.gcd_one_left y)
  . exact Nat.coprime_self_add_right.mpr (Nat.gcd_one_right x)
