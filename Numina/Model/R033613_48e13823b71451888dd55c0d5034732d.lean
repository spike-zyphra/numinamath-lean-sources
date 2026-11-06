import Mathlib


theorem number_theory_15711 (a b c : ℕ) (s : Set ℕ) (hs : s = {a, b, c}) (hs_card : s.ncard = 3)
    (hdigit : ∀ x ∈ s, x ∈ Set.Ioo 0 6)
    (h : Nat.ofDigits 6 [c, b, a] + Nat.ofDigits 6 [a, c, b] + Nat.ofDigits 6 [b, a, c] =
      Nat.ofDigits 6 [0, a, a, a]) :
    b + c = Nat.ofDigits 6 [5] := by

  have h1 : a ∈ s := by
    rw [hs] 
    simp 
  have h2 : b ∈ s := by
    rw [hs] 
    simp 
  have h3 : c ∈ s := by
    rw [hs] 
    simp 
  have h4 : a ∈ Set.Ioo 0 6 := by
    apply hdigit a
    exact h1
  have h5 : b ∈ Set.Ioo 0 6 := by
    apply hdigit b
    exact h2
  have h6 : c ∈ Set.Ioo 0 6 := by
    apply hdigit c
    exact h3
  rcases h4 with ⟨ha1, ha2⟩
  rcases h5 with  ⟨hb1, hb2⟩
  rcases h6 with  ⟨hc1, hc2⟩
  simp [Nat.ofDigits, List.foldl] at h ⊢
  have h7 : b + c = 5 * a := by
    omega
  have h8 : a ≤ 2 := by
    omega
  have h9 : a = 1 ∨ a = 2 := by
    omega
  rcases h9 with (ha | ha)
  · -- a = 1
    have h10 : b + c = 5 := by
      rw [show a = 1 by omega] at h7
      omega
    have h21 : Nat.ofDigits 6 [5] = 5 := by
      simp [Nat.ofDigits, List.foldl]
    omega
  · -- a = 2
    have h10 : b + c = 10 := by
      rw [show a = 2 by omega] at h7
      omega
    have h11 : b ≤ 5 := by omega
    have h12 : c ≤ 5 := by omega
    have h13 : b = 5 := by
      omega
    have h14 : c = 5 := by
      omega
    have h15 : s = {a, b, c} := by exact_mod_cast hs
    have h17 : s = {2, 5} := by
      rw [show a = 2 by omega, show b = 5 by omega, show c = 5 by omega] at h15
      rw [h15]
      aesop
    have h18 : s.ncard = 2 := by
      rw [h17]
      simp
    omega