import Mathlib

/- Solve the system of equations

$1-x_{1} x_{2} x_{3}=0$

$1+x_{2} x_{3} x_{4}=0$

$1-x_{3} x_{4} x_{5}=0$,

$1+x_{4} x_{5} x_{6}=0$

...

$1-x_{47} x_{48} x_{49}=0$,

$1+x_{48} x_{49} x_{50}=0$,

$1-x_{49} x_{50} x_{1}=0$

$1+x_{50} x_{1} x_{2}=0$. -/
theorem algebra_232175 (x : Fin 50 → ℝ) (hx : ∀ i, 1 - x i * x ((i + 1) % 50) * x ((i + 2) % 50) = 0)
    (hx' : ∀ i, 1 + x ((i + 1) % 50) * x ((i + 2) % 50) * x ((i + 3) % 50) = 0) :
    ∀ i, x i = (-1 : ℝ) ^ (i.1 + 1) := by
  -- Get the first equation: 1 - x₀ * x₁ * x₂ = 0
  have h1 := hx 0
  -- Get the second equation: 1 + x₁ * x₂ * x₃ = 0
  have h2 := hx' 0
  -- Get the third equation: 1 - x₁ * x₂ * x₃ = 0
  have h3 := hx 1
  -- Simplify the expressions
  simp at h1 h2 h3
  -- Use nonlinear arithmetic to solve the system
  nlinarith
