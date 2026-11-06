import Mathlib

theorem other_90036 (n : ℕ) (hn : n > 0) (a : ℕ → ℝ)
    (hsum7 : ∀ i, i + 6 < n → ∑ j ∈ Finset.range 7, a (i + j) < 0)
    (hsum11 : ∀ i, i + 10 < n → ∑ j ∈ Finset.range 11, a (i + j) > 0) :
    n ≤ 16 := by
  by_contra h
  push_neg at h
  have h17 : n ≥ 17 := by omega
  have h2_0 : ∑ j in Finset.range 7, a (0 + j) < 0 := hsum7 0 (by omega)
  have h2_1 : ∑ j in Finset.range 7, a (1 + j) < 0 := hsum7 1 (by omega)
  have h2_2 : ∑ j in Finset.range 7, a (2 + j) < 0 := hsum7 2 (by omega)
  have h2_3 : ∑ j in Finset.range 7, a (3 + j) < 0 := hsum7 3 (by omega)
  have h2_4 : ∑ j in Finset.range 7, a (4 + j) < 0 := hsum7 4 (by omega)
  have h2_5 : ∑ j in Finset.range 7, a (5 + j) < 0 := hsum7 5 (by omega)
  have h2_6 : ∑ j in Finset.range 7, a (6 + j) < 0 := hsum7 6 (by omega)
  have h2_7 : ∑ j in Finset.range 7, a (7 + j) < 0 := hsum7 7 (by omega)
  have h2_8 : ∑ j in Finset.range 7, a (8 + j) < 0 := hsum7 8 (by omega)
  have h2_9 : ∑ j in Finset.range 7, a (9 + j) < 0 := hsum7 9 (by omega)
  have h2_10 : ∑ j in Finset.range 7, a (10 + j) < 0 := hsum7 10 (by omega)
  have h8_0 : ∑ j in Finset.range 11, a (0 + j) > 0 := hsum11 0 (by omega)
  have h8_1 : ∑ j in Finset.range 11, a (1 + j) > 0 := hsum11 1 (by omega)
  have h8_2 : ∑ j in Finset.range 11, a (2 + j) > 0 := hsum11 2 (by omega)
  have h8_3 : ∑ j in Finset.range 11, a (3 + j) > 0 := hsum11 3 (by omega)
  have h8_4 : ∑ j in Finset.range 11, a (4 + j) > 0 := hsum11 4 (by omega)
  have h8_5 : ∑ j in Finset.range 11, a (5 + j) > 0 := hsum11 5 (by omega)
  have h8_6 : ∑ j in Finset.range 11, a (6 + j) > 0 := hsum11 6 (by omega)
  have h22 : (∑ j in Finset.range 7, a (0 + j)) + (∑ j in Finset.range 7, a (1 + j)) + (∑ j in Finset.range 7, a (2 + j)) + (∑ j in Finset.range 7, a (3 + j)) + (∑ j in Finset.range 7, a (4 + j)) + (∑ j in Finset.range 7, a (5 + j)) + (∑ j in Finset.range 7, a (6 + j)) + (∑ j in Finset.range 7, a (7 + j)) + (∑ j in Finset.range 7, a (8 + j)) + (∑ j in Finset.range 7, a (9 + j)) + (∑ j in Finset.range 7, a (10 + j)) < 0 := by
    linarith [h2_0, h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7, h2_8, h2_9, h2_10]
  have h23 : (∑ j in Finset.range 11, a (0 + j)) + (∑ j in Finset.range 11, a (1 + j)) + (∑ j in Finset.range 11, a (2 + j)) + (∑ j in Finset.range 11, a (3 + j)) + (∑ j in Finset.range 11, a (4 + j)) + (∑ j in Finset.range 11, a (5 + j)) + (∑ j in Finset.range 11, a (6 + j)) > 0 := by
    linarith [h8_0, h8_1, h8_2, h8_3, h8_4, h8_5, h8_6]
  have h24 : (∑ j in Finset.range 7, a (0 + j)) + (∑ j in Finset.range 7, a (1 + j)) + (∑ j in Finset.range 7, a (2 + j)) + (∑ j in Finset.range 7, a (3 + j)) + (∑ j in Finset.range 7, a (4 + j)) + (∑ j in Finset.range 7, a (5 + j)) + (∑ j in Finset.range 7, a (6 + j)) + (∑ j in Finset.range 7, a (7 + j)) + (∑ j in Finset.range 7, a (8 + j)) + (∑ j in Finset.range 7, a (9 + j)) + (∑ j in Finset.range 7, a (10 + j)) = (∑ j in Finset.range 11, a (0 + j)) + (∑ j in Finset.range 11, a (1 + j)) + (∑ j in Finset.range 11, a (2 + j)) + (∑ j in Finset.range 11, a (3 + j)) + (∑ j in Finset.range 11, a (4 + j)) + (∑ j in Finset.range 11, a (5 + j)) + (∑ j in Finset.range 11, a (6 + j)) := by 
    norm_num [Finset.sum_range_succ]
    <;> ring
  linarith [h24, h22, h23]