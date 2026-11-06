import Mathlib 

open Real 

namespace algebra_601369

theorem Cauchy_Schwarz_Ineq (a b c d : ℝ):
    (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  have h : 0 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2
  calc
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2 = (a * d - b * c) ^ 2 := by ring
    _ ≥ 0 := pow_two_nonneg (a * d - b * c)
  calc
    (a * c + b * d) ^ 2  = (a * c + b * d) ^ 2 + 0 := by rw [add_zero]
    _ ≤ (a * c + b * d) ^ 2 + ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) - (a * c + b * d) ^ 2) :=
    (add_le_add_iff_left _).2 h
    _ = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by ring

theorem Cauchy_Schwarz_Ineq' {a b c d : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) :
    (√a * √c + √b * √d) ^ 2 ≤ (a + b) * (c + d) := by
  conv_rhs => rw [← sq_sqrt ha, ← sq_sqrt hb, ← sq_sqrt hc, ← sq_sqrt hd]
  apply Cauchy_Schwarz_Ineq 

theorem Cauchy_Schwarz_Ineq'' {a b c d : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) :
    (√a * √c + √b * √d) ^ 2 ≤ (a + b) * (c + d) := by
  apply Cauchy_Schwarz_Ineq' ha.le hb.le hc.le hd.le

lemma subineq {x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0) : 
    (1 + y * z + z * x) / (1 + x + y) ^ 2 ≥ z / (x + y + z) := by 
  have h1 : z * (x + y) > 0 := by nlinarith 
  have h2 : (x + y) / z > 0 := by apply div_pos <;> linarith
  have leq1 := Cauchy_Schwarz_Ineq'' (b := 1) (d := 1) h1 (by norm_num) h2 (by norm_num) 
  simp only [sqrt_one, mul_one] at leq1 
  have eq1 : √(z * (x + y)) * √((x + y) / z) = (x + y) := by
    rw [← sqrt_mul h1.le ((x + y) / z)]   
    have : (z * (x + y)) * ((x + y) / z) = (x + y) ^ 2 := by field_simp ; ring 
    rw [this] 
    rw [sqrt_sq (by nlinarith)]
  rw [eq1] at leq1  
  field_simp at leq1 
  rw [le_div_iff₀' hz] at leq1 
  rw [ge_iff_le, div_le_div_iff₀ (by nlinarith) (by nlinarith)] 
  rw [show 1 + x + y = x + y + 1 by abel]
  calc
    _ ≤ (z * (x + y) + 1) * (x + y + z) := leq1 
    _ = _ := by ring 
  
end algebra_601369

open algebra_601369

/-
102. Let $x, y, z$ be positive numbers, prove:
$$\frac{1+y z+z x}{(1+x+y)^{2}}+\frac{1+z x+x y}{(1+y+z)^{2}}+\frac{1+x y+y z}{(1+z+x)^{2}} \geqslant 1$$
(2010 Japan Mathematical Olympiad)-/
theorem algebra_601369 {x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0) :
    (1 + y * z + z * x) / (1 + x + y) ^ 2 + (1 + z * x + x * y) / (1 + y + z) ^ 2 + (1 + x * y + y * z) / (1 + z + x) ^ 2 ≥ 1 := by
  -- By the Cauchy inequality, we have $(z(x+y)+1)\left(\frac{x+y}{z}+1\right) \geqslant(-x+y+\mathrm{F})^{2}$, 
  -- so $\frac{1+y z+z x}{(1+x+y)^{2}} \geqslant \frac{z}{x+y \mp z}$, 
  -- similarly $\frac{1+z x+x y}{(1+y+z)^{2}} \geqslant \frac{x}{x+y+z}, \frac{1+x y+y z}{(1+z+x)^{2}} \geqslant$ $\frac{y}{x+y+z}$, 
  have geq1 := subineq hx hy hz 
  have geq2 := subineq hy hz hx
  have geq3 := subineq hz hx hy 
  -- adding the three inequalities we get $$\frac{1+y z+z x}{(1+x+y)^{2}}+\frac{1+z x+x y}{(1+y+z)^{2}}+\frac{1+x y+y z}{(1+z+x)^{2}} \geqslant 1
  calc 
    _ ≥ z / (x + y + z) + x / (y + z + x) + y / (z + x + y) := by linarith only [geq1, geq2, geq3]    
    _ = (x + y + z) / (x + y + z) := by linear_combination
    _ = 1 := by field_simp 
  
