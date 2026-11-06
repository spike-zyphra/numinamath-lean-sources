import Mathlib

/- 2. Determine all triples $(x, y, z)$ of positive integers with $x \leq y \leq z$ that satisfy


$$

\left(1+\frac{1}{x}\right)\left(1+\frac{1}{y}\right)\left(1+\frac{1}{z}\right)=3

$$
 -/
theorem number_theory_172484 (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≤ y) (hyz : y ≤ z) :
    (1 + 1 / x : ℚ) * (1 + 1 / y : ℚ) * (1 + 1 / z : ℚ) = 3 ↔
    (x = 1 ∧ y = 3 ∧ z = 8) ∨ (x = 1 ∧ y = 4 ∧ z = 5) ∨ (x = 2 ∧ y = 2 ∧ z = 3) := by
  constructor
  -- first assume the equation
  . rintro h
    -- w must have x < 3 otherwise the lhs is <= (4/3)^3
    have hx : x < 3 := by
      by_contra h3
      simp at h3
      have : (3:ℚ) ≤ (4/3) * (4/3) * (4/3)  := by calc
        3 = (1 + 1/x: ℚ) * (1 + 1/y: ℚ) * (1 + 1/z: ℚ) := by rw [← h]
        _ ≤ (1 + 1/3) * (1 + 1/3) * (1 + 1/3) := by
          gcongr
          . norm_cast
          . norm_cast; linarith
          . norm_cast; linarith
        _ = (4/3) * (4/3) * (4/3) := by norm_num
      norm_num at this
    -- do case work on x
    interval_cases x
    . simp
      -- for x = 1, do case work on y
      match y with
      -- y = 0 is not possible
      | 0 => contradiction
      -- y = 1 brings z = -4, not acceptable
      | 1 =>
        have : 1 / (z: ℚ) = 1 / (-4) := by linarith
        simp at this
        norm_cast at this
      -- y = 2 brings 1/z = 0, not acceptable
      | 2 =>
        have : 1 / (z: ℚ) = 0 := by linarith
        simp at this
        linarith
      -- y = 3 brings z = 8
      | 3 =>
        have : 1 / (z:ℚ) = 1 / 8 := by linarith
        simp at this
        norm_cast at this
        simp [this]
      -- y = 4 brings z = 5
      | 4 =>
        have : 1 / (z:ℚ) = 1 / 5 := by linarith
        simp at this
        norm_cast at this
        simp [this]
      -- for y >= 5 lhs <= 2 * 6/5 * 6/5, not possible
      | n + 5 =>
        push_cast at h
        have : 3 ≤ (2 * (6/5) * (6/5) : ℚ) := by calc
          3 = 2 * (1 + 1 / (n + 5) : ℚ) * (1 + 1 / z : ℚ) := by rw [← h]; ring
          _ ≤ 2 * (1 + 1 / 5) * (1 + 1 / 5) := by
            gcongr
            repeat norm_cast; linarith
          _ = 2 * (6/5) * (6/5) := by norm_num
        linarith
    . simp
      -- for x = 2, do casework on y
      match y with
      -- y = 0 is not possible
      | 0 => contradiction
      -- y = 1 is also not possible
      | 1 => norm_num at hxy
      -- y = 2 brings z = 3
      | 2 =>
        have : 1 / (z:ℚ) = 1 / 3 := by linarith
        simp at this
        norm_cast at this
      -- for y >= 3 lhs <= 3/2 * 4/3 * 4/3, impossible
      | n + 3 =>
        push_cast at h
        have : 3 ≤ ((3/2) * (4/3) * (4/3) : ℚ) := by calc
          3 = (1 + 1 / 2) * (1 + 1 / (n + 3) : ℚ) * (1 + 1 / z : ℚ) := by nth_rw 1 [← h]
          _ ≤ (1 + 1 / 2) * (1 + 1 / 3) * (1 + 1 / 3) := by
            gcongr
            repeat norm_cast; linarith
          _ = (3/2) * (4/3) * (4/3) := by norm_num
        linarith
    -- when using the values plugged into equation, the equation is satisfied
  . rintro h
    obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ := h
    all_goals norm_num