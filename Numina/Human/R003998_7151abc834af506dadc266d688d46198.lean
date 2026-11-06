import Mathlib

/-
78. The smallest natural number whose digits sum to 218 is an $n$-digit number, then $n=$
-/

theorem number_theory_228453 (x:ℕ) (h :IsLeast {n:ℕ | (Nat.digits 10 n).sum = 218} x) :
(Nat.digits 10 x).length = 25 := by

  unfold IsLeast lowerBounds at h
  simp at h
  obtain ⟨h1,h2⟩ := h
  
  --We first prove that n ≥ 25. 
  have cla1: ∀ k ∈ (Nat.digits 10 x), k < 10 := by
    exact fun k a => Nat.digits_lt_base' a
  have cla2: ∀ k ∈ (Nat.digits 10 x), k ≤ 9 := by 
    intro k hk
    have : k < 10 := cla1 k hk
    omega
  --Even if every digit is 9, we still need 25 digits, so n ≥ 25.
  have cla3: (Nat.digits 10 x).sum ≤ ((Nat.digits 10 x).length)*9 := by 
    have t1: (Nat.digits 10 x).sum ≤ (List.replicate (Nat.digits 10 x).length 9).sum := by 
      refine List.Forall₂.sum_le_sum ?_
      rw [@List.forall₂_iff_get]
      simp

      intro i h1 h2
      have : (Nat.digits 10 x)[i] ∈ (Nat.digits 10 x) := by simp
      apply cla2 at this
      exact this

    have t2: (List.replicate (Nat.digits 10 x).length 9).sum = (Nat.digits 10 x).length*9 := by
      rw [List.sum_replicate]; 
      ring
    linarith
  rw [h1] at cla3
  have : 25 ≤ ((Nat.digits 10 x).length) := by omega

  --On the other hand, 25 is enough, so n ≤ 25.
  --We use the following number.
  let m := 9999999999999999999999992
  have mdig : (Nat.digits 10 m).sum = 218 := by 
    simp [m]
  have xlem : x ≤ m := by 
    apply h2
    exact mdig
  have : (Nat.digits 10 x).length ≤ (Nat.digits 10 m).length := by exact Nat.le_digits_len_le 10 x m (h2 mdig)
  have mdiglen : (Nat.digits 10 m).length = 25 := by
    simp [m]
  rw [mdiglen] at this
  linarith
  