import Mathlib

theorem number_theory_126902 (a : ℕ → ℤ) (ha : ∀ n, a n ≠ 0)
    (hpos : ∀ n, n + 6 < n' → ∑ i ∈ Finset.range 7, a (n + i) > 0)
    (hneg : ∀ n, n + 10 < n' → ∑ i ∈ Finset.range 11, a (n + i) < 0) :
    n' ≤ 16 := by 
  by_contra h
  push_neg at h
  have h1 := hpos 0 (by omega)
  have h2 := hpos 1 (by omega)
  have h3 := hpos 2 (by omega)
  have h4 := hpos 3 (by omega)
  have h5 := hpos 4 (by omega)
  have h6 := hpos 5 (by omega)
  have h7 := hpos 6 (by omega)
  have h8 := hpos 7 (by omega)
  have h9 := hpos 8 (by omega)
  have h10 := hpos 9 (by omega)
  have h11 := hpos 10 (by omega)
  have h12 := hneg 0 (by omega)
  have h13 := hneg 1 (by omega)
  have h14 := hneg 2 (by omega)
  have h15 := hneg 3 (by omega)
  have h16 := hneg 4 (by omega)
  have h17 := hneg 5 (by omega)
  have h18 := hneg 6 (by omega)
  norm_num [Finset.sum_range_succ] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
  all_goals omega