import Mathlib

theorem algebra_166644 (x : ℝ) (hx : x > 0) (h : 2 * ⌊x⌋ = x + (x - ⌊x⌋)) :
    x = 3 / 2 := by
  have h1 : (⌊x⌋ : ℝ) ≤ x := by exact Int.floor_le x
  have h2 : x < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x
  -- We assume that $2 \cdot \lfloor x \rfloor = x + (x - \lfloor x \rfloor)$
  have eq1 : x = 3 / 2 * (⌊x⌋ : ℝ) := by
    have eq2 : (2 * (⌊x⌋ : ℝ) : ℝ) = x + (x - (⌊x⌋ : ℝ)) := by
      simpa using h
    nlinarith
  have h5 : ⌊x⌋ ≤ 2 := by
    by_contra h6
    push_neg at h6
    have h6' : ⌊x⌋ ≥ 3 := by
      omega
    have h7 : (⌊x⌋ : ℝ) ≥ (3 : ℝ) := by exact_mod_cast h6'
    -- Contradicts with `x < \lfloor x \rfloor + 1`.
    nlinarith [eq1, h7, h2]
  have h6 : ⌊x⌋ ≥ 1 := by
    by_contra h7
    push_neg at h7
    have h7' : ⌊x⌋ ≤ 0 := by
      omega
    have h8 : (⌊x⌋ : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h7'
    -- Contradicts with `x > 0`.
    nlinarith [eq1, h8, hx]
  have h8 : ⌊x⌋ = 1 ∨ ⌊x⌋ = 2 := by
    omega
  rcases h8 with h9 | h10
  · -- $\lfloor x \rfloor = 1$
    have h9' : (⌊x⌋ : ℝ) = (1 : ℝ) := by exact_mod_cast h9
    rw [h9'] at eq1
    nlinarith
  · -- $\lfloor x \rfloor = 2$
    have h10' : (⌊x⌋ : ℝ) = (2 : ℝ) := by exact_mod_cast h10
    rw [h10'] at eq1
    have eq3 : x = (3 : ℝ) := by
      nlinarith
    have h7 : x < ((⌊x⌋ + 1 : ℝ)) := by
      exact_mod_cast (show x < ⌊x⌋ + 1 by apply Int.lt_floor_add_one)
    -- Contradicts with `Int.lt_floor_add_one`
    nlinarith [eq3, h7]