import Mathlib

theorem algebra_287539 (y : ℝ → ℝ) (hy : y = fun x => (17 - x) * (19 - x) * (19 + x) * (17 + x)) :
    IsLeast {y x | x : ℝ} (-1296) := by 
  constructor
  · -- Show that -1296 is achievable by y
    use Real.sqrt 325
    have h1 : Real.sqrt 325 ^ 2 = 325 := Real.sq_sqrt (by linarith)
    rw [hy]
    have h2 : (17 - Real.sqrt 325) * (17 + Real.sqrt 325) = -36 := by
      calc
        (17 - Real.sqrt 325) * (17 + Real.sqrt 325) = 17^2 - (Real.sqrt 325)^2 := by ring
        _ = 289 - (Real.sqrt 325)^2 := by norm_num
        _ = 289 - 325 := by rw [h1]
        _ = -36 := by norm_num
    have h3 : (19 - Real.sqrt 325) * (19 + Real.sqrt 325) = 36 := by
      calc
        (19 - Real.sqrt 325) * (19 + Real.sqrt 325) = 19^2 - (Real.sqrt 325)^2 := by ring
        _ = 361 - (Real.sqrt 325)^2 := by norm_num
        _ = 361 - 325 := by rw [h1]
        _ = 36 := by norm_num
    simp [h2, h3]
    <;> nlinarith
  · -- Show that -1296 is indeed the least value
    intro z
    rintro ⟨x, hx⟩
    rw [hy] at hx
    simp only [add_mul, mul_add, mul_sub, sub_mul] at hx
    nlinarith [sq_nonneg (x ^ 2 - 325)]