import Mathlib

theorem algebra_322689 (f : ℝ → ℝ) (hf : f = fun x => 9^x + 9^(-x) - 2 * (3^x + 3^(-x))) :
    IsLeast (Set.image f (Set.univ : Set ℝ)) (-2) := by
  constructor
  · -- Show that -2 is indeed in the image
    use 0
    simp [hf]
    all_goals norm_num
  · -- Show that -2 is the least element in the image
    intro y
    rintro ⟨x, hx⟩
    simp [hf] at hx
    have h1 : (3 : ℝ) ^ x > 0 := by positivity
    have h2 : (3 : ℝ) ^ (-x : ℝ) > 0 := by positivity
    -- Prove that 3^x * 3^(-x) = 1
    have h3 : (3 : ℝ) ^ x * (3 : ℝ) ^ (-x : ℝ) = 1 := by
      have h4 : (3 : ℝ) ^ x * (3 : ℝ) ^ (-x : ℝ) = (3 : ℝ) ^ (x + (-x : ℝ)) := by 
        rw [← Real.rpow_add]
        ring_nf
        all_goals linarith
      rw [h4]
      norm_num
    -- Prove the expressions for 9^x and 9^(-x)
    have h4 : (9 : ℝ) ^ x = ((3 : ℝ) ^ x) ^ 2 := by
      calc
        (9 : ℝ) ^ x = (3 ^ (2 : ℕ)) ^ x := by norm_num
        _ = (3 : ℝ) ^ (2 * x : ℝ) := by rw [← Real.rpow_natCast]; rw [← Real.rpow_mul]; ring; all_goals linarith
        _ = ((3 : ℝ) ^ x) ^ 2 := by rw [← Real.rpow_natCast]; rw [← Real.rpow_mul]; ring; all_goals linarith
    have h5 : (9 : ℝ) ^ (-x : ℝ) = ((3 : ℝ) ^ (-x : ℝ)) ^ 2 := by
      calc
        (9 : ℝ) ^ (-x : ℝ) = (3 ^ (2 : ℕ)) ^ (-x : ℝ) := by norm_num
        _ = (3 : ℝ) ^ (2 * (-x : ℝ)) := by rw [← Real.rpow_natCast]; rw [← Real.rpow_mul]; ring; all_goals linarith
        _ = ((3 : ℝ) ^ (-x : ℝ)) ^ 2 := by rw [← Real.rpow_natCast]; rw [← Real.rpow_mul]; ring; all_goals linarith
    -- Prove the expression for 9^x + 9^(-x)
    have h6 : (9 : ℝ) ^ x + (9 : ℝ) ^ (-x : ℝ) = ((3 : ℝ) ^ x + (3 : ℝ) ^ (-x : ℝ)) ^ 2 - 2 := by
      rw [h4, h5]
      have h7 : ((3 : ℝ) ^ x) ^ 2 + ((3 : ℝ) ^ (-x : ℝ)) ^ 2 = ((3 : ℝ) ^ x + (3 : ℝ) ^ (-x : ℝ)) ^ 2 - 2 := by
        nlinarith [show (3 : ℝ) ^ x * (3 : ℝ) ^ (-x : ℝ) = 1 by linarith [h3]]
      linarith [h7]
    -- Prove that 3^x + 3^(-x) ≥ 2
    have h7 : (3 : ℝ) ^ x + (3 : ℝ) ^ (-x : ℝ) ≥ 2 := by
      have h8 : (3 : ℝ) ^ x > 0 := h1
      have h9 : (3 : ℝ) ^ (-x : ℝ) > 0 := h2
      have h10 : (3 : ℝ) ^ x * (3 : ℝ) ^ (-x : ℝ) = 1 := h3
      nlinarith [sq_nonneg ((3 : ℝ) ^ x - (3 : ℝ) ^ (-x : ℝ)), sq_nonneg ((3 : ℝ) ^ x - 1), sq_nonneg ((3 : ℝ) ^ (-x : ℝ) - 1)]
    -- Prove that f(x) ≥ -2
    have h8 : (9 : ℝ) ^ x + (9 : ℝ) ^ (-x : ℝ) - 2 * ((3 : ℝ) ^ x + (3 : ℝ) ^ (-x : ℝ)) ≥ -2 := by
      have h9 : (9 : ℝ) ^ x + (9 : ℝ) ^ (-x : ℝ) = ((3 : ℝ) ^ x + (3 : ℝ) ^ (-x : ℝ)) ^ 2 - 2 := h6
      nlinarith [sq_nonneg ((3 : ℝ) ^ x + (3 : ℝ) ^ (-x : ℝ) - 2), sq_nonneg ((3 : ℝ) ^ x - (3 : ℝ) ^ (-x : ℝ)), h7]
    linarith [h8, hx]