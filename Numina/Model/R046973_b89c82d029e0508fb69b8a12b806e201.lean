import Mathlib

theorem algebra_8227 {a b x y : ℝ} (h₀ : a + b = 3) (h₁ : x + y = 5)
    (h₂ : a * x + b * y = 7) :
    (a ^ 2 + b ^ 2) * x * y + a * b * (x ^ 2 + y ^ 2) = 56 := by
  have eq3 : (a + b) * (x + y) * (a * x + b * y) = 105 := by
    have h3 : a + b = 3 := h₀
    have h4 : x + y = 5 := h₁
    have h5 : a * x + b * y = 7 := h₂
    rw [h3, h4, h5]
    norm_num
  have eq4 : (a ^ 2 + b ^ 2) * x * y + a * b * (x ^ 2 + y ^ 2) = 56 := by
    have h3 : (a + b) * (x + y) * (a * x + b * y) = 105 := eq3
    nlinarith [sq_nonneg (a - b), sq_nonneg (x - y), sq_nonneg (a * y - b * x), 
          sq_nonneg (a * x - b * y), sq_nonneg (a * b), sq_nonneg (x * y), 
          h₀, h₁, h₂, 
          sq_nonneg (a + b - 3), sq_nonneg (x + y - 5), 
          sq_nonneg ( (a * x + b * y) - 7 )
        ]
  linarith [eq4]