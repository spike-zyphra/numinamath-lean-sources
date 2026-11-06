import Mathlib

theorem algebra_19319 {f g : ℝ → ℝ} (hf : f = fun x => x + 2) (hg : g = fun x => x ^ 2) : {x | f (g x) = g (f x)} = {-1/2} := by
  ext x
  simp [hf, hg]
  constructor
  · -- Assume f(g(x)) = g(f(x)), prove x = -1/2
    intro h
    have h2 : x^2 + 2 = (x + 2)^2 := by linarith
    have h3 : x^2 + 2 = x^2 + 4 * x + 4 := by 
      linarith [h2]
    have h4 : 2 = 4 * x + 4 := by 
      linarith [h3]
    have h5 : -2 = 4 * x := by 
      linarith [h4]
    linarith
  · -- Assume x = -1/2, prove f(g(x)) = g(f(x))
    intro h
    rw [h]
    norm_num