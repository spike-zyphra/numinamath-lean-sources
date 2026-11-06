import Mathlib

theorem number_theory_19028{d_one d_ten: ℕ}
  (one_digit: d_one = (∏ i ∈ Finset.range 100, (2^(i + 1))) % 10)
  (ten_digit: d_ten = ((∏ i ∈ Finset.range 100, (2^(i + 1))) / 10) % 10):
  d_one * d_ten = 8 := by 
  rw [one_digit, ten_digit]
  native_decide