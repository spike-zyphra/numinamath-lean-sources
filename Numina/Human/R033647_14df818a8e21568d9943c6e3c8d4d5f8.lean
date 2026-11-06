import Mathlib

/-Marie is thinking of a multiple of 63, while Jay is thinking of a factor of 63. They happen to be thinking of the same number. There are two possibilities for the number that each of them is thinking of, one positive and one negative. Find the product of these two numbers.-/
theorem algebra_21542 {x : ℤ} (h : 63 ∣ x ∧ x ∣ 63) :
    x * (-x) = -3969 := by
  -- show that x.natAbs = 63
  have hx0 : x.natAbs = 63 := by
    obtain ⟨hx1, hx2⟩ := h
    apply Int.natAbs_eq_of_dvd_dvd hx1 at hx2
    calc
      x.natAbs = Int.natAbs 63 := by rw [hx2]
      _ = 63 := by norm_num
  -- calculate the results by x ^ 2 = x.natAbs ^ 2
  calc
    x * (-x) = -(x ^ 2) := by ring_nf
    _ = -(x.natAbs ^ 2) := by rw [Int.natAbs_sq]
    _ = -(63 ^ 2) := by rw [hx0]; norm_cast
    _ = -3969 := by norm_num