import Mathlib

theorem algebra_148098 {x : ℤ} (hx : x ≠ 4) (h : 3 * x / (x - 4) = 4 ∧ 3 * x % (x - 4) = x - 12) :
    x = 14 := by
  have h1 : 3 * x / (x - 4) = 4 := h.1
  have h2 : 3 * x % (x - 4) = x - 12 := h.2
  have h3 : x - 4 ≠ 0 := by
    intro h4
    apply hx
    omega

  have h4 : 3 * x = (x - 4) * 4 + (x - 12) := by
    rw [← Int.ediv_add_emod (3 * x) (x - 4)]
    rw [h1, h2]
    all_goals ring_nf <;> omega
  -- Now we have the equation 3 * x = (x - 4) * 4 + (x - 12)
  -- Let's solve the equation
  -- Expanding right side: 4(x - 4) + (x - 12) = 4x - 16 + x - 12 = 5x - 28
  -- Therefore, 3x = 5x - 28
  -- Solving: -2x = -28, so x = 14
  have eq3 : x = 14 := by
    omega
  exact_mod_cast eq3