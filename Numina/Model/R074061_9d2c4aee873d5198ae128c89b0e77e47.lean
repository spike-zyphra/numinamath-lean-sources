import Mathlib

theorem number_theory_281228 (x : Fin 7 → ℕ) (hx : StrictMono x)
    (hxp : ∀ i, x i > 0) (hsum : ∑ i, x i = 158) :
    x 0 + x 1 + x 2 ≤ 60 := by
  have hx0 : x 0 > 0 := hxp 0
  have hx1 : x 1 > 0 := hxp 1
  have hx2 : x 2 > 0 := hxp 2
  have hx3 : x 3 > 0 := hxp 3
  have hx4 : x 4 > 0 := hxp 4
  have hx5 : x 5 > 0 := hxp 5
  have hx6 : x 6 > 0 := hxp 6
  have h1 : x 0 < x 1 := by
    apply hx
    simp
  have h2 : x 1 < x 2 := by
    apply hx
    simp
  have h3 : x 2 < x 3 := by
    apply hx
    simp
  have h4 : x 3 < x 4 := by
    apply hx
    simp
  have h5 : x 4 < x 5 := by
    apply hx
    simp
  have h6 : x 5 < x 6 := by
    apply hx
    simp
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hsum
  omega