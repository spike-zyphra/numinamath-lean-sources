import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_599155 (a b c : ℝ)
  (ha : a ∈ Icc 0 2) (hb : b ∈ Icc 0 2) (hc : c ∈ Icc 0 2)
  (hsum : a + b + c = 5) :
  a^2 + b^2 + c^2 ≤ 9 := by
  rcases ha with ⟨ha0, ha2⟩
  rcases hb with ⟨hb0, hb2⟩
  rcases hc with ⟨hc0, hc2⟩
  nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2), hsum, mul_nonneg (show 0 ≤ (2 - a) by linarith) (show 0 ≤ (2 - b) by linarith), mul_nonneg (show 0 ≤ (2 - a) by linarith) (show 0 ≤ (2 - c) by linarith), mul_nonneg (show 0 ≤ (2 - b) by linarith) (show 0 ≤ (2 - c) by linarith)]