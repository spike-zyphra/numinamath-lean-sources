import Mathlib

/- A cubic polynomial $f$ satisfies $f(0)=0, f(1)=1, f(2)=2, f(3)=4$. What is $f(5)$? -/
theorem algebra_22179 {f : ℝ → ℝ} (hf : ∃ a b c d, a ≠ 0 ∧ f = fun x => a*x^3 + b*x^2 + c*x + d)
    (h0 : f 0 = 0) (h1 : f 1 = 1) (h2 : f 2 = 2) (h3 : f 3 = 4) :
    f 5 = 15 := by 
  obtain ⟨a,b,c,d,ha,hf⟩ := hf
  simp_all
  linarith