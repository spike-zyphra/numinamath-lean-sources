import Mathlib

theorem algebra_290520 :
  {c : ℝ | ∃ x y : ℝ, x ≠ 0 ∧ y ≠ 0 ∧ 5*x^2-2*x+c=0 ∧ 5*y^2-2*y+c=0 ∧ x/y=-3/5} = {-3} := by
  ext c
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume there exist non-zero x and y such that both are roots and x/y = -3/5, prove c = -3
    rintro ⟨x, y, hx, hy, h1, h2, h3⟩
    
    have h4 : x = -3 / 5 * y := by
      have hne : y ≠ 0 := hy
      field_simp [hne] at h3
      linarith

    rw [h4] at h1

    have eq1' : 9 * y ^ 2 + 6 * y + 5 * c = 0 := by
      nlinarith [h1]

    -- Now we have two equations:
    -- 1. `9 * y ^ 2 + 6 * y + 5 * c = 0` (eq1')
    -- 2. `5 * y ^ 2 - 2 * y + c = 0` (h2)
    -- Subtract the second from the first to eliminate c:
    -- `9 * y ^ 2 + 6 * y + 5 * c - (5 * y ^ 2 - 2 * y + c) = 0`
    -- `4 * y ^ 2 + 8 * y + 4 * c = 0`
    -- `y ^ 2 + 2 * y + c = 0`

    have eq3 : 4 * y ^ 2 + 8 * y + 4 * c = 0 := by
      nlinarith [h2, eq1']

    -- Factor out 4:
    have eq4 : y ^ 2 + 2 * y + c = 0 := by
      linarith

    -- We solve for c from h2, and substitute into eq4.
    -- From h2: `5y^2 - 2y + c = 0`, so `c = -5y^2 + 2y`.
    -- Substitute into eq4: `y^2 + 2 * y + (-5y^2 + 2y) = 0`.
    -- This simplifies to: `-4y^2 + 4y = 0` or ` -4 * y * (y - 1) = 0`.
    -- Since `y ≠ 0` (from hy), we have `y = 1`.

    have eq5 : c = -5 * y ^ 2 + 2 * y := by
      nlinarith

    rw [eq5] at eq4
    have eq6 : -4 * y ^ 2 + 4 * y = 0 := by 
      nlinarith

    -- From eq6: ` -4 * y * (y - 1) = 0 `.
    -- Since `y ≠ 0`, we have `y - 1 = 0` so `y = 1`.

    have eq7 : y = 1 := by 
      have hne : y ≠ 0 := hy
      have : y * (y - 1) = 0 := by 
        nlinarith
      cases' (mul_eq_zero.mp this) with hy1 hy2
      · -- case y = 0, which contradicts hne
        exfalso
        tauto
      · -- y - 1 = 0, so y = 1
        linarith

    rw [eq7] at eq5
    linarith

  · -- Now the reverse direction: if c = -3, then there exist such x and y.
    intro h
    rw [h]

    use -3 / 5, 1

    constructor
    · -- Show x ≠ 0
      norm_num

    constructor
    · -- Show y ≠ 0
      norm_num

    constructor
    · -- Show 5 * x ^ 2 - 2 * x - 3 = 0
      norm_num

    constructor
    · -- Show 5 * y ^ 2 - 2 * y - 3 = 0
      norm_num

    · -- Show x / y = -3 / 5
      norm_num