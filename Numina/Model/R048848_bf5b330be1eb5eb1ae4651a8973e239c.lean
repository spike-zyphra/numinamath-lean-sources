import Mathlib

open Set Real

theorem algebra_10933 {m n : ℝ} (hm : m ∈ Icc 0 1) (hn : n ∈ Icc 0 1)
    (hM : ∀ x ∈ Icc 0 1, x ∈ Icc m (m + 3 / 4) → x ∈ Icc m (m + 3 / 4) ∩ Icc 0 1)
    (hN : ∀ x ∈ Icc 0 1, x ∈ Icc (n - 1 / 3) n → x ∈ Icc (n - 1 / 3) n ∩ Icc 0 1) :
    (m + 3 / 4 - n + 1 / 3) ≥ 1 / 12 := by 
  rcases hm with ⟨hm0, hm1⟩
  rcases hn with ⟨hn0, hn1⟩ 
  linarith