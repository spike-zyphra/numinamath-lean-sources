import Mathlib

theorem algebra_149424 {k k1 : ℝ} (hk : 0 < k) (hk1 : k ≠ 1)
    (h : ∀ x y, y = k * x + 1 → ∃ x' y', x' = y + 1 ∧ y' = k1 * x' + 1 ∧
      x ^ 2 / 4 + y' ^ 2 = 1) :
    k * k1 = -5 / 3 := by

  have h1 := h 0 1 (by 
    norm_num 
    <;> nlinarith
  )

  rcases h1 with ⟨x1, y1, hx1, hy1, heq1⟩
  
  have h2 := h 2 (2*k+1) (by 
    ring_nf 
  )
  rcases h2 with ⟨x2, y2, hx2, hy2, heq2⟩
  
  have h3 := h (-2) (1 - 2*k) (by 
    ring_nf 
  )
  rcases h3 with ⟨x3, y3, hx3, hy3, heq3⟩

  norm_num at heq1 heq2 heq3 
  nlinarith [sq_pos_of_ne_zero (show (k - 1 : ℝ) ≠ 0 by
    by_contra h'
    apply hk1
    linarith 
  ), sq_nonneg (k - 1), sq_nonneg (k1 + 5 / (3 * 1))
  ]