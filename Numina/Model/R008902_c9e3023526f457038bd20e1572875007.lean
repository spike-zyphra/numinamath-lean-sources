import Mathlib

theorem algebra_21440 {e o : ℝ → ℝ} (he : Function.Even e) (ho : Function.Odd o)
    (h : ∀ x, e x + x ^ 2 = o x) (f : ℝ → ℝ) (hf : ∀ x, f x = e x + o x) :
    f 2 = -4 := by
  have h2 := h 2
  have h2' := h (-2)
  have he2 : e (-2) = e 2 := he 2
  have ho2 : o (-2) = - o 2 := ho 2
  norm_num [he2, ho2] at h2 h2'
  have he2_val : e 2 = -4 := by 
    linarith
  have ho2_val : o 2 = 0 := by
    linarith [h2, he2_val]
  have hf2 : f 2 = e 2 + o 2 := hf 2
  rw [hf2]
  rw [he2_val, ho2_val]
  all_goals norm_num