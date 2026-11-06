import Mathlib

open Finset

theorem number_theory_114702 {n : ℕ} (hn : n = 2006) :
    {k | k ∈ range (n + 1) ∧ (Nat.choose n k) % 3 = 0}.ncard = 1764 ∧
    {k | k ∈ range (n + 1) ∧ (Nat.choose n k) % 3 = 1}.ncard = 122 ∧
    {k | k ∈ range (n + 1) ∧ (Nat.choose n k) % 3 = 2}.ncard = 121 := by
  rw [hn]
  have h1 : {k | k ∈ range (2006 + 1) ∧ (Nat.choose 2006 k) % 3 = 0}.ncard = 1764 := by
    have h1 : {k | k ∈ range (2006 + 1) ∧ (Nat.choose 2006 k) % 3 = 0} = Finset.filter (fun k => (Nat.choose 2006 k) % 3 = 0) (Finset.Iio (2006 + 1 : ℕ)) := by
      ext k
      simp
      <;> try tauto
    rw [h1]
    rw [Finset.filter]
    simp [Finset.Iio]
    <;> native_decide
  have h2 : {k | k ∈ range (2006 + 1) ∧ (Nat.choose 2006 k) % 3 = 1}.ncard = 122 := by
    have h2 : {k | k ∈ range (2006 + 1) ∧ (Nat.choose 2006 k) % 3 = 1} = Finset.filter (fun k => (Nat.choose 2006 k) % 3 = 1) (Finset.Iio (2006 + 1 : ℕ)) := by
      ext k
      simp
      <;> try tauto
    rw [h2]
    rw [Finset.filter]
    simp [Finset.Iio]
    <;> native_decide
  have h3 : {k | k ∈ range (2006 + 1) ∧ (Nat.choose 2006 k) % 3 = 2}.ncard = 121 := by
    have h3 : {k | k ∈ range (2006 + 1) ∧ (Nat.choose 2006 k) % 3 = 2} = Finset.filter (fun k => (Nat.choose 2006 k) % 3 = 2) (Finset.Iio (2006 + 1 : ℕ)) := by
      ext k
      simp
      <;> try tauto
    rw [h3]
    rw [Finset.filter]
    simp [Finset.Iio]
    <;> native_decide
  exact ⟨h1, h2, h3⟩