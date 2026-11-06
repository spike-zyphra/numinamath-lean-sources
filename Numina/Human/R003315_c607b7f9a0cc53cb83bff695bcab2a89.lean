import Mathlib

/- 7. (15 points) A stone with a mass of $m=6002$ was thrown at an angle $\alpha$ to the horizontal with an initial velocity of $v_{0}=20 \mathrm{M} / \mathrm{s}$. In the presence of air resistance proportional to the stone's velocity (proportionality coefficient $k=0.1(\mathrm{H} \cdot \mathrm{s}) / \mathrm{m})$, the maximum height reached by the stone is $h=10$ m. The work done by the resistance force over this time interval is $A=30$ Joules. Determine the acceleration of the stone at the highest point of the trajectory. The acceleration due to gravity is $g=10 \mathrm{M} / \mathrm{s}^{2}$. -/
theorem calculus_168957 {m v₀ v g h A ax k ay a : ℝ}
  (h₁ : 0.5 * m * v₀^2 = 0.5 * m * v^2 + m * g * h + A)
  (h₂ : ax = k * v / m ∧ ay = g)
  (h₃ : a^2 = ax^2 + ay^2)
  (ha : a ≥ 0)
  (hv : v ≥ 0)
  (h_data : m = 6002 ∧ v₀ = 20 ∧ k = 0.1 ∧ h = 10 ∧ A = 30 ∧ g = 10) : a = √((1 / 10 * (√600170 / √3001) / 6002) ^ 2 + 100) := by
  -- substitute in the data
  simp [h_data] at *
  -- use the first equation to find v
  have v_val : 600170 / 3001 = v^2
  · norm_num at h₁
    linarith [h₁]
  -- substitute into the second equation and conclude
  rw [←Real.sqrt_eq_iff_eq_sq] at v_val
  rw [h₂.1, h₂.2, ←v_val] at h₃
  symm at h₃
  rw [←Real.sqrt_eq_iff_eq_sq] at h₃
  rw [←h₃]
  norm_num
  repeat positivity