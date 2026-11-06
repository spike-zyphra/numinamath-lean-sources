import Mathlib

open Real
open scoped BigOperators

/- 2. (POL) Let $a, b$, and $c$ be the lengths of a triangle whose area is $S$. Prove that  $$ a^{2}+b^{2}+c^{2} \geq 4 S \sqrt{3} $$  In what case does equality hold? -/
theorem inequalities_24509 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) (S : ℝ)
  (hS : S = (1/2) * a * b * sin (arccos ((a^2 + b^2 - c^2)/(2*a*b)))) :
  a^2 + b^2 + c^2 ≥ 4 * S * sqrt 3 ∧
  (a^2 + b^2 + c^2 = 4 * S * sqrt 3 ↔ (a = b ∧ b = c)) := by

  -- Using the formula for S, we rewrite our equations.
  let θ := arccos ((a^2 + b^2 - c^2)/(2*a*b))
  have eq1 : S = (1/2) * a * b * sin θ := hS
  have c2 : c^2 = a^2+b^2 - 2*a*b*cos θ := by
    simp [θ]
    have :  cos (arccos ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b))) = ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) := by 
      apply Real.cos_arccos
      rw [le_div_iff₀]
      nlinarith
      positivity
      rw [div_le_iff₀]
      nlinarith
      positivity
    rw [this]
    field_simp
  rw [eq1,c2]
  --We get that we just need to consider (a-b)^2 + 2ab(1-cos(θ - π /3)).
  --It is obviously non-negative.
  have : a ^ 2 + b ^ 2 + (a ^ 2 + b ^ 2 - 2 * a * b * cos θ) - 4 * (1 / 2 * a * b * sin θ) * √3 = 2 * ((a-b)^2 + 2*a*b*(1-cos (θ - π/3))) := by
    rw [Real.cos_sub]
    simp
    ring_nf
  have b1: 0 ≤ (a-b)^2 := by exact sq_nonneg (a - b)
  have b2: 0 ≤ 2 * a * b * (1 - cos (θ - π / 3)) := by 
    have : 0 ≤ 2 * a := by linarith only [ha]
    have t1: 0 ≤ 2 * a * b := by exact (mul_nonneg_iff_of_pos_right hb).mpr this
    have : cos (θ - π / 3) ≤ 1 := by exact cos_le_one (θ - π / 3)
    have t2: 0 ≤ 1 - cos (θ - π / 3) := by linarith only [this]
    exact Left.mul_nonneg t1 t2
  have : 0 ≤ 2 * ((a-b)^2 + 2*a*b*(1-cos (θ - π/3))) := by 
    simp
    linarith
  
  constructor
  linarith

  --And when we have the equality, we have a=b and cos (θ - π /3) = 1, which leads to a=b=c.
  constructor
  intro h
  have eq : 2 * ((a-b)^2 + 2*a*b*(1-cos (θ - π/3))) = 0 := by linarith
  simp at eq
  have eq1 : (a-b)^2 = 0 := by linarith
  simp at eq1
  have aeb : a = b := by linarith only [eq1]
  have eq2 : (cos (θ - π/3)) = 1 := by 
    simp [aeb] at eq
    rcases eq with eq | eq
    linarith
    linarith
  have eq3 : (cos θ) = 1/2 := by 
    have : sin (θ - π /3) = 0 := by refine sin_eq_zero_iff_cos_eq.mpr ?_; simp [eq2]
    have eq : cos (θ) = cos (θ - π /3 + π/3) := by ring_nf
    rw [cos_add] at eq
    simp [eq2,this] at eq ⊢
    exact eq
  simp [aeb, eq3] at c2
  ring_nf at c2
  have bec : b = c := by nlinarith
  tauto

  --For the other direction, if a=b=c, then the equality is achieved. This follows from simple calculation.
  intro h
  obtain ⟨aeb,bec⟩ := h
  have eq1: cos θ = 1/2 := by 
    simp [aeb,bec] at c2
    ring_nf at c2
    have : c^2 * (2-1-cos θ *2) = 0 := by linarith only [c2]
    simp at this
    rcases this with t | t
    linarith
    linarith
  have eq2: sin θ = √3 / 2 := by 
    rw [sin_arccos]
    simp [aeb,bec]
    field_simp
    ring_nf
    have : sqrt (c ^ 4 * 3)  = c ^ 2 * √3 := by 
      refine (sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
      simp
      exact sq_pos_of_pos hc
      ring_nf
      field_simp
    rw [this]
  simp [aeb,bec,eq1,eq2]
  ring_nf
  simp
    