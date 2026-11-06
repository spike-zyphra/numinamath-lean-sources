import Mathlib

theorem number_theory_23481 (x y : ℤ) (hx : x ≡ 4 [ZMOD 19]) (hy : y ≡ 7 [ZMOD 19]) :
    ((x + 1)^2 * (y + 5)^3) ≡ 13 [ZMOD 19] := by
  have hx1 : x + 1 ≡ 5 [ZMOD 19] := by
    have h1 : x ≡ 4 [ZMOD 19] := hx
    simp [Int.ModEq] at h1 ⊢
    omega
  have hy1 : y + 5 ≡ 12 [ZMOD 19] := by
    have h1 : y ≡ 7 [ZMOD 19] := hy
    simp [Int.ModEq] at h1 ⊢
    omega
  have hx2 : (x + 1)^2 ≡ 6 [ZMOD 19] := by
    have h1 : x + 1 ≡ 5 [ZMOD 19] := hx1
    have h2 : (x + 1)^2 ≡ 5^2 [ZMOD 19] := by
      apply Int.ModEq.pow
      exact h1
    simp [Int.ModEq] at h2 ⊢
    omega
  have hy2 : (y + 5)^3 ≡ 18 [ZMOD 19] := by
    have h1 : y + 5 ≡ 12 [ZMOD 19] := hy1
    have h2 : (y + 5)^3 ≡ 12^3 [ZMOD 19] := by
      apply Int.ModEq.pow
      exact h1
    norm_num [Int.ModEq] at h2 ⊢
    omega
  have h3 : ((x + 1)^2 * (y + 5)^3) ≡ (6 * 18) [ZMOD 19] := by
    apply Int.ModEq.mul
    exact hx2
    exact hy2
  simp [Int.ModEq] at h3 ⊢
  omega