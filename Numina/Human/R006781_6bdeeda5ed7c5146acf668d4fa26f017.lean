import Mathlib

open Nat 

theorem number_theory_641097 (X Y : ℕ) (A B C N₁ N₂ : ℕ) (hX : X ∈ Finset.Icc 1 9) (hY : Y ∈ Finset.Icc 1 9)
  (hA : A ∈ Finset.Icc 0 9) (hB : B ∈ Finset.Icc 0 9) (hC : C ∈ Finset.Icc 0 9)
  (hN₁ : N₁ = ofDigits 10 [1, B, 2, 5, A, 4, X])
  (hN₂ : N₂ = ofDigits 10 [C, 4, B, A, 6, 2, Y])
  (dvd1 : 3 ∣ N₁) (dvd2 : 3 ∣ N₂) : C ≡ (X - Y) [ZMOD 3] := by 
  have eq1 : N₁ = (X * 10 ^ 6 + 4 * 10 ^ 5 + A * 10 ^ 4 + 5 * 10 ^ 3 + 2 * 10 ^ 2 + B * 10 + 1) := by 
    rw [hN₁, ofDigits_cons, ofDigits_cons, ofDigits_cons, ofDigits_cons, ofDigits_cons, ofDigits_cons]
    simp
    ring
  have eq2 : N₂ = (Y * 10 ^ 6 + 2 * 10 ^ 5 + 6 * 10 ^ 4 + A * 10 ^ 3 + B * 10 ^ 2 + 4 * 10 + C) := by 
    rw [hN₂, ofDigits_cons, ofDigits_cons, ofDigits_cons, ofDigits_cons, ofDigits_cons, ofDigits_cons]
    simp 
    ring
  rw [eq1] at dvd1
  rw [eq2] at dvd2
  zify at dvd1 dvd2
  have modeq1 : ↑X * 10 ^ 6 + 4 * 10 ^ 5 + ↑A * 10 ^ 4 + 5 * 10 ^ 3 + 2 * 10 ^ 2 + ↑B * 10 + 1 ≡ X + 4 + A + 5 + 2 + B + 1 [ZMOD 3] := by 
    have aux1 : X * 10 ^ 6 ≡ X [ZMOD 3] := by 
      calc 
        _ ≡ X * 1 ^ 6 [ZMOD 3] := by 
          apply Int.ModEq.mul_left 
          exact rfl
        _ ≡ X [ZMOD 3] := by 
          simp
    have aux2 : 4 * 10 ^ 5 ≡ 4 [ZMOD 3] := by 
      rfl 
    have aux3 : A * 10 ^ 4 ≡ A [ZMOD 3] := by 
      calc 
        _ ≡ A * 1 ^ 4 [ZMOD 3] := by 
          apply Int.ModEq.mul_left
          exact rfl
        _ ≡ A [ZMOD 3] := by 
          simp
    have aux4 : 5 * 10 ^ 3 ≡ 5 [ZMOD 3] := by 
      rfl
    have aux5 : 2 * 10 ^ 2 ≡ 2 [ZMOD 3] := by 
      rfl
    have aux6 : B * 10 ≡ B [ZMOD 3] := by 
      apply Int.modEq_of_dvd
      ring_nf 
      omega
    unfold Int.ModEq at aux1 aux2 aux3 aux4 aux5 aux6 ⊢ 
    omega
  have modeq2 : (Y * 10 ^ 6 + 2 * 10 ^ 5 + 6 * 10 ^ 4 + A * 10 ^ 3 + B * 10 ^ 2 + 4 * 10 + C) ≡ Y + 2 + 6 + A + B + 4 + C [ZMOD 3] := by 
    have aux1 : Y * 10 ^ 6 ≡ Y [ZMOD 3] := by 
      calc 
        _ ≡ Y * 1 ^ 6 [ZMOD 3] := by 
          apply Int.ModEq.mul_left 
          rfl 
        _ ≡ Y [ZMOD 3] := by 
          simp 
    have aux2 : 2 * 10 ^ 5 ≡ 2 [ZMOD 3] := by 
      rfl 
    have aux3 : 6 * 10 ^ 4 ≡ 6 [ZMOD 3] := by 
      rfl 
    have aux4 : A * 10 ^ 3 ≡ A [ZMOD 3] := by 
      calc 
        _ ≡ A * 1 ^ 3 [ZMOD 3] := by 
          apply Int.ModEq.mul_left 
          rfl 
        _ ≡ A [ZMOD 3] := by 
          simp 
    have aux5 : B * 10 ^ 2 ≡ B [ZMOD 3] := by 
      calc 
        _ ≡ B * 1 ^ 2 [ZMOD 3] := by 
          apply Int.ModEq.mul_left 
          rfl 
        _ ≡ B [ZMOD 3] := by 
          simp 
    have aux6 : 4 * 10 ≡ 4 [ZMOD 3] := by
      rfl 
    unfold Int.ModEq at aux1 aux2 aux3 aux4 aux5 aux6 ⊢ 
    omega
  have modeq3 : ↑X * 10 ^ 6 + 4 * 10 ^ 5 + ↑A * 10 ^ 4 + 5 * 10 ^ 3 + 2 * 10 ^ 2 + ↑B * 10 + 1 ≡ 0 [ZMOD 3] := by 
    exact Int.modEq_zero_iff_dvd.mpr dvd1
  obtain modeq4 := Int.modEq_zero_iff_dvd.mpr dvd2
  have modeq5 : ↑X + 4 + ↑A + 5 + 2 + ↑B + 1 
    ≡ ↑Y + 2 + 6 + ↑A + ↑B + 4 + ↑C [ZMOD 3] := by 
    calc 
      _ ≡ ↑X * 10 ^ 6 + 4 * 10 ^ 5 + ↑A * 10 ^ 4 + 5 * 10 ^ 3 + 2 * 10 ^ 2 + ↑B * 10 + 1 [ZMOD 3] := by 
        exact Int.ModEq.symm modeq1
      _ ≡ 0 [ZMOD 3]:= by exact modeq3
      _ ≡ ↑Y * 10 ^ 6 + 2 * 10 ^ 5 + 6 * 10 ^ 4 + ↑A * 10 ^ 3 + ↑B * 10 ^ 2 + 4 * 10 + ↑C [ZMOD 3] := by 
        exact Int.ModEq.symm modeq4
      _ ≡ ↑Y + 2 + 6 + ↑A + ↑B + 4 + ↑C [ZMOD 3] := by 
        exact modeq2
  obtain dvd3 := Int.ModEq.dvd modeq5
  ring_nf at dvd3
  rw [show ↑Y + ((C : ℤ) - ↑X) = C - (X - Y) by ring] at dvd3
  obtain modeq6 := Int.modEq_of_dvd dvd3
  exact Int.ModEq.symm modeq6