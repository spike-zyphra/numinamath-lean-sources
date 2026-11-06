import Mathlib

theorem algebra_605619{a b c: ℝ}(aneb: a ≠ b)
  (cpos: 0 < c)(heq: a^4-2019*a = b^4 - 2019*b ∧ b^4-2019*b = c):
  -√c < a*b ∧ a*b < 0 := by
  rcases heq with ⟨h1, h2⟩
  have h3 : a ^ 4 - 2019 * a = b ^ 4 - 2019 * b := by linarith
  have h4 : a ^ 4 - b ^ 4 = 2019 * (a - b):= by linarith [h1]
  have h5 : a ^ 4 - b ^ 4 = (a - b) * (a + b) * (a ^ 2 + b ^ 2):= by 
    ring_nf
  -- Therefore, we can solve to get $(a + b)(a^2 + b^2) = 2019$
  have h6 : ((a + b) * (a ^ 2 + b ^ 2) )= 2019:= by 
    have hne : a - b ≠ 0 := by 
      by_contra h
      have : a = b := by 
        nlinarith 
      contradiction 
    apply (mul_left_inj' hne).mp 
    linarith [h4, h5]

  have h8 : a * b < 0 := by 
    nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by 
      intro h 
      apply aneb 
      nlinarith 
    ), sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a * b), sq_nonneg (a - b), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a + b), sq_nonneg (a - b)
    ]
  
  have h9 : (a * b) ^ 2 < c := by 
    nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by 
      intro h 
      apply aneb 
      nlinarith 
    ), sq_nonneg (a + b), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a * b), sq_nonneg (a - b), pow_two_nonneg (a - b), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a + b), sq_nonneg (a - b)
    ]

  have h10 : -√c < a * b := by
    have h11 : (a * b) ^ 2 < c := h9 
    have h12 : √c > 0 := Real.sqrt_pos.mpr cpos 
    nlinarith [Real.sqrt_nonneg c, Real.sq_sqrt (show 0 ≤ c by linarith), sq_nonneg (a * b)
    ]

  exact ⟨h10, h8⟩