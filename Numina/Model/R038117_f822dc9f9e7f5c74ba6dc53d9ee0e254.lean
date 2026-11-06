import Mathlib

theorem number_theory_47811 (a b : Fin 600 → Fin 600 → ℕ)
    (ha : ∀ i j, a i j = if i = 0 ∨ i = 599 then 2 ^ (j.1 + 1) else 0)
    (hb : ∀ i j, b i j = if i = 1 ∨ i = 598 then 2 ^ (j.1 + 1) else 0) :
    ∑ i, ∑ j, a i j + ∑ i, ∑ j, b i j ≡ 0 [ZMOD 9] := by
  simp [Int.ModEq, Finset.sum_fin_eq_sum_range, Finset.sum_congr, ha, hb]
  <;> native_decide