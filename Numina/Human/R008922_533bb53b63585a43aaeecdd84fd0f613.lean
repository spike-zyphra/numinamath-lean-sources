import Mathlib

/- PROBLEM: Let f be a linear function for which f(6)−f(2)=12. What is f(12)−f(2)? -/
theorem algebra_96555 
  {f : ℝ → ℝ} 
  (hf : ∃ a b, f = fun x => a * x + b) 
  (h : f 6 - f 2 = 12) : 
  f 12 - f 2 = 30 := 
by {
  rcases hf with ⟨a, b, hlin⟩
  rw [hlin] at h
  simp at h
  ring_nf at h
  rw [hlin]
  simp
  ring_nf
  linarith
}