import Mathlib

/-Solve the equation :
$(3+x) \times 30\% = 4.8$  -/
theorem algebra_9396_1 {x : ℝ} (h : (3 + x) * 30 / 100 = 4.8)  :
  x = 13 := by
    -- (1) $(3+x) \times 30\% = 4.8$
    --     $(3+x) \times 0.3 \div 0.3 = 4.8 \div 0.3$
    --                           $3+x = 16$
    --                         $3+x-3 = 16-3$
    --                             $x = 13$
    have := (div_eq_iff (by simp)).1 h
    ring_nf at this
    linarith

/- Solve the equation : $5 : x = \frac{9}{2} : \frac{8}{5}$-/
theorem algebra_9396_2 {x : ℝ} (h : 5 / x = 9 / 2 / (8 / 5)) :
  x = 16 / 9 := by
    -- (2) $5 : x = \frac{9}{2} : \frac{8}{5}$
    --       $\frac{9}{2}x = 5 \times \frac{8}{5}$
    --        $\frac{9}{2}x = 8$
    --  $\frac{9}{2}x \times \frac{2}{9} = 8 \times \frac{2}{9}$
    --              $x = \frac{16}{9}$
    field_simp at h
    rw [div_eq_iff] at h
    linarith
    intro x0
    simp [x0] at h
