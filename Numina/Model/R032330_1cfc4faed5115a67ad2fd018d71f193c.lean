import Mathlib 

theorem Algebra_611043 {a b c d : ℝ} (h1 : |a - b| + |c - d| = 99) (h2 : |a - c| + |b - d| = 1) 
  : |a - d| + |b - c| = 99 := by
  cases' abs_cases (a - b) with h11 h11 <;> 
  cases' abs_cases (c - d) with h12 h12 <;> 
  cases' abs_cases (a - c) with h13 h13 <;> 
  cases' abs_cases (b - d) with h14 h14 <;> 
  cases' abs_cases (a - d) with h15 h15 <;> 
  cases' abs_cases (b - c) with h16 h16
  <;> linarith