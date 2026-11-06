import Mathlib

/- Find the number of ordered 2012-tuples of integers $\left(x_{1}, x_{2}, \ldots, x_{2012}\right)$, with each integer between 0 and 2011 inclusive, such that the sum $x_{1}+2 x_{2}+3 x_{3}+\cdots+2012 x_{2012}$ is divisible by 2012 .-/
theorem number_theory_609046 : 
  ∀ (x : Fin 2011 → ℕ), ∃! (x1 : Fin 2012), 
  2012 ∣ ∑ (i : Fin 2011), ((i + 2 : ℕ) * (x i) ) + x1 := by 
  intro x
  by_cases h : (∑ i : Fin 2011, (i + 2 : ℕ) * ↑(x i)) % 2012 = 0 
  use 0 
  constructor
  simp
  omega
  intro j h'
  have dvd_aux : 2012 ∣ (∑ i : Fin 2011, (i + 2 : ℕ) * ↑(x i)) := by omega
  omega
  have : (∑ i : Fin 2011, (i + 2 : ℕ) * ↑(x i)) % 2012 > 0 := by 
    omega
  have ineq : (2012 - (∑ i : Fin 2011, (i + 2 : ℕ) * ↑(x i)) % 2012) < 2012 := by 
    omega
  use ⟨(2012 - (∑ i : Fin 2011, (i + 2 : ℕ) * ↑(x i)) % 2012), ineq⟩
  constructor
  simp
  omega
  simp
  intro y hy
  apply Fin.eq_of_val_eq
  simp
  omega