import Mathlib

theorem number_theory_6303 (a : ℕ → ℤ) (ha : ∀ i, a i ≡ 1 [ZMOD 2]) (ha' : ∀ i, a i ≡ -1 [ZMOD 3]) (ha'' : ∀ i, a i ≡ 1 [ZMOD 5]) (ha''' : ∀ i, a i ≡ -1 [ZMOD 7]) :
    ∀ i, a i ≡ 41 [ZMOD 11] ∨ a i ≡ 251 [ZMOD 11] ∨ a i ≡ 461 [ZMOD 11] ∨ a i ≡ 671 [ZMOD 11] ∨ a i ≡ 881 [ZMOD 11] ∨ a i ≡ 1091 [ZMOD 11] ∨ a i ≡ 1301 [ZMOD 11] ∨ a i ≡ 1511 [ZMOD 11] ∨ a i ≡ 1721 [ZMOD 11] ∨ a i ≡ 1931 [ZMOD 11] ∨ a i ≡ 2141 [ZMOD 11] := by
  intro i
  have h1 := ha i
  have h2 := ha' i
  have h3 := ha'' i
  have h4 := ha''' i
  norm_num [Int.ModEq] at h1 h2 h3 h4 ⊢
  omega