import Mathlib

theorem algebra_298851 {a b c : ℝ} (ha : a ≠ 0) (f : ℝ → ℝ) (hf : f = fun x => a * x ^ 2 + b * x + c)
    (h : ∃ x, f x = 4096) (h' : f (x + 1) = 4227) (h'' : f (x + 2) = 4356) (h''' : f (x + 3) = 4489)
    (h'''' : f (x + 4) = 4624) (h''''' : f (x + 5) = 4761) :
    f (x + 2) ≠ 4096 := by
  intro h_contra
  have h1 : f (x + 2) = 4356 := h''
  rw [h1] at h_contra
  norm_num at h_contra