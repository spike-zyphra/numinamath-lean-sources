import Mathlib

theorem number_theory_6987
(m n : ℕ)
(h : 0 < m ∧ 0 < n)
(h1 : m.gcd n = 1)
: ArithmeticFunction.moebius (m * n) = ArithmeticFunction.moebius m * ArithmeticFunction.moebius n := by 
  have h2 : m > 0 := h.1
  have h3 : n > 0 := h.2
  -- Use the multiplicativity of the Möbius function
  rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime]
  · -- Show that the Möbius function is multiplicative
    apply ArithmeticFunction.isMultiplicative_moebius
  · -- Show m and n are coprime
    exact h1