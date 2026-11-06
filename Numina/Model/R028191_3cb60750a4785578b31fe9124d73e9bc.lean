import Mathlib


open Finset


lemma lemma_1
    (x y z : ℕ)
    (hx : x.Prime)
    (hy : y.Prime)
    (hz : z.Prime)
    (hle : x ≤ y ∧ y ≤ z)
    (hsum : x ^ 2 + y ^ 2 + z ^ 2 = 2019) :
    x ≠ 5 := by
  by_contra h
  have hx2 : x = 5 := by
    tauto
  have h1 : x ≤ y := hle.left
  have h2 : y ≤ z := hle.right
  have h3 : 5 ≤ y := by
    omega
  have h4 : 5 ≤ z := by
    omega
  rw [show x = 5 by omega] at hsum
  have h5 : y ≤ 44 := by
    nlinarith
  have h6 : z ≤ 44 := by
    nlinarith
  interval_cases y <;> interval_cases z
    <;> norm_num at hsum h1 h2 h3 h4 h5 h6
    <;> norm_num [Nat.pow_two] at hsum h1 h2 h3 h4 h5 h6
    <;> norm_num at hx hy hz
    <;> try { contradiction }


theorem number_theory_11274 :
    {(x, y, z) : ℕ × ℕ × ℕ | x.Prime ∧ y.Prime ∧ z.Prime ∧ x ≤ y ∧ y ≤ z ∧ x ^ 2 + y ^ 2 + z ^ 2 = 2019}.ncard = 6 := by
  have h1 : {(x, y, z) : ℕ × ℕ × ℕ | x.Prime ∧ y.Prime ∧ z.Prime ∧ x ≤ y ∧ y ≤ z ∧ x ^ 2 + y ^ 2 + z ^ 2 = 2019} = Finset.filter (fun s : ℕ × ℕ × ℕ =>
    (Nat.Prime (s.1) ∧ Nat.Prime (s.2.1) ∧ Nat.Prime (s.2.2) ∧ s.1 ≤ s.2.1 ∧ s.2.1 ≤ s.2.2 ∧ s.1 ^2 + s.2.1^2 + s.2.2^2 = 2019)
  ) (Finset.Icc (0 : ℕ) 44 ×ˢ Finset.Icc (0 : ℕ) 44 ×ˢ Finset.Icc (0 : ℕ) 44) := by
    ext ⟨x, y, z⟩
    simp
    intro hx hy hz h1 h2 h3
    have h4 : x ≤ 44 := by
      nlinarith
    have h5 : y ≤ 44 := by
      nlinarith
    have h6 : z ≤ 44 := by
      nlinarith
    tauto
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc]
  <;> try { native_decide }