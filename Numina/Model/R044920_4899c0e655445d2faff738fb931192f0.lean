import Mathlib

/- Xiao Hu and Xiao Tu calculated the product of two two-digit numbers, Jia and Yi. Xiao Hu misread the unit digit of Jia, and the result of his calculation was $1274$; Xiao Tu misread the tens digit of Jia, and the result of his calculation was $819$. The number Jia is ___        ___. -/
theorem algebra_7452 {x y : ℕ} (hx : x ∈ Finset.Icc 10 99) (hy : y ∈ Finset.Icc 10 99)
    (h1 : x * y = 1274) (h2 : (10 * x + y) * (10 * y + x) = 819) :
    x = 93 := by
  rw [Finset.mem_Icc] at hx hy
  rcases hx with ⟨hx10, hx99⟩
  rcases hy with ⟨hy10, hy99⟩
  have h4 : (10 * x + y) * (10 * y + x) ≥ 100 * (x * y) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (10 * x - y)]
  have h6 : x * y = 1274 := h1
  have h7 : (10 * x + y) * (10 * y + x) ≥ 127400 := by
    nlinarith [h6, h4]
  nlinarith [h2, h7]