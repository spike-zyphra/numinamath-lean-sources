import Mathlib

theorem number_theory_6817 (x y z : ℤ) :
    4*x-9*y+5*z=8 ↔ ∃ u v : ℤ, x=-6+10*v+9*u ∧ y=-3+5*v+4*u ∧ z=1+v := by
  constructor
  · -- Assume $4x - 9y + 5z = 8$, then there exist $u$ and $v$ such that $x = -6 + 10v + 9u$, $y = -3 + 5v + 4u$, and $z = 1 + v$.
    intro h
    have h2 : 4 * x - 9 * y + 5 * z = 8 := h
    use (y + 8 - 5 * z) / 4, z - 1
    constructor
    · -- Show that x = -6 + 10 * v + 9 * u
      omega
    constructor
    · -- Show that y = -3 + 5 * v + 4 * u
      omega
    · -- Show that z = 1 + v
      omega
  · -- Show that if there exist $u$ and $v$ such that $x = -6 + 10v + 9u$, $y = -3 + 5v + 4u$, and $z = 1 + v$, then $4x - 9y + 5z = 8$.
    rintro ⟨u, v, hx, hy, hz⟩
    rw [hx, hy, hz]
    omega