import Mathlib

/- A truck started from city $A$ to city $B$ at midnight, and a car started from city $B$ to city $A$ (on the same route) at $t_{1}$. They met at $t_{2}$. The car arrived at its destination $r$ hours later than the truck. - After finishing their business, they started back, and met again at $t_{3}$, and finally arrived home at the same time. When did they arrive? -

Numerical data: $t_{1}=2^{\mathrm{h}} 40^{\mathrm{m}}, t_{2}=4^{\mathrm{h}}, r=0^{\mathrm{h}} 40^{\mathrm{m}}, t_{3}=14^{\mathrm{h}}$. -/
theorem algebra_156370 {r s t₁ t₂ t₃ v V x : ℝ}
  (vpos : v > 0)
  (Vpos : V > 0)
  (tpos : t₂ > 0)
  (tpos2 : t₂ - t₁ > 0)
  (h₁ : s = v * t₂ + V * (t₂ - t₁))
  (h₂ : s / v = s / V + t₁ - r)
  (h₃ : v * (x - t₃) + V * (x - t₃) = v * t₂ + V * (t₂ - t₁)) :
  v / V = (r + √(r^2 + 4 * t₂ * (t₂ - t₁))) / (2 * t₂) ∧ x = t₃ + t₂ - t₁ / (1 + v/V) := by
  -- substitute equation 1 into equation 2
  rw [h₁] at h₂
  rw [div_eq_iff_mul_eq (ne_of_gt vpos)] at h₂
  -- solve quadratic in v/V
  have disc : discrim t₂ (-r) (-(t₂ - t₁)) = (√(r^2 + 4 * t₂ * (t₂ - t₁)))^2
  · unfold discrim; rw [Real.sq_sqrt (by nlinarith)]; ring
  rw [pow_two] at disc
  have quad : t₂ * (v / V)^2 + -r * (v / V) + -(t₂ - t₁) = 0
  · calc
    _ = ((v * t₂ + V * (t₂ - t₁)) / V + t₁ - r) * v / V - (v * t₂ + V * (t₂ - t₁)) / V := by field_simp; ring
    _ = 0 := by rw [h₂]; ring
  rw [pow_two, quadratic_eq_zero_iff (ne_of_gt tpos) disc (v / V), neg_neg] at quad
  cases quad with
  | inl quad =>
    -- positive root: substitute into equation 3
    constructor; exact quad; calc
      x = (v * (x - t₃) + V * (x - t₃)) / (v + V) + t₃ := by field_simp; ring
      _ = (v * t₂ + V * (t₂ - t₁)) / (v + V) + t₃      := by rw [h₃]
      _ = t₃ + t₂ - t₁ / (1 + v / V)                   := by field_simp; ring
  | inr quad =>
    -- negative root is not meaningful
    have ineq : √(r^2 + 4 * t₂ * (t₂ - t₁)) > r := by apply Real.lt_sqrt_of_sq_lt; nlinarith
    have vVneg : v / V < 0
    · calc
      v / V = (r - √(r^2 + 4 * t₂ * (t₂ - t₁))) / (2 * t₂) := by rw [quad]
      _ < 0 := by exact div_neg_of_neg_of_pos (by linarith) (by linarith)
    have vVpos : v / V > 0 := div_pos vpos Vpos
    linarith