import Mathlib

/- 8.3. (Canada, 81). Prove that the equation


$$

[x]+[2 x]+[4 x]+[8 x]+[16 x]+[32 x]=12345

$$


has no solutions. -/
theorem number_theory_121121 : ¬∃ x : ℝ, ⌊x⌋ + ⌊2 * x⌋ + ⌊4 * x⌋ + ⌊8 * x⌋ + ⌊16 * x⌋ + ⌊32 * x⌋ = 12345 := by
  -- proof by contradiction
  by_contra h
  obtain ⟨x, hx⟩ := h
  -- first prove x > 0 as otherwise x ≤ 0 implies lhs is ≤ 0, which is false
  have : x > 0 := by
    by_contra hx_nonpos
    simp at hx_nonpos
    have : ⌊x⌋ ≤ 0 := by exact Int.floor_nonpos hx_nonpos
    have aux (k : ℕ) : ⌊k * x⌋ ≤ 0 := by
      refine Int.floor_nonpos ?_
      calc
        k * x ≤ k * 0 := by gcongr
        _ = 0 := by simp
    have : ⌊2*x⌋ ≤ 0 := by exact_mod_cast aux 2
    have : ⌊4*x⌋ ≤ 0 := by exact_mod_cast aux 4
    have : ⌊8*x⌋ ≤ 0 := by exact_mod_cast aux 8
    have : ⌊16*x⌋ ≤ 0 := by exact_mod_cast aux 16
    have : ⌊32*x⌋ ≤ 0 := by exact_mod_cast aux 32
    linarith
  -- next prove k * ⌊x⌋ ≤ ⌊k * x⌋ by noting that ⌊k * ⌊x⌋⌋ = k * ⌊x⌋
  have aux₁ (k: ℕ) :  k * ⌊x⌋ ≤ ⌊k * x⌋ := by
    have : k * ⌊x⌋ ≤ k * x := by gcongr; exact Int.floor_le x
    have := Int.floor_le_floor this
    convert this
    norm_cast
    exact Eq.symm (Int.floor_intCast (↑k * ⌊x⌋))
  -- next prove ⌊k * x⌋ < k * ⌊x⌋ + k
  have aux₂ (k: ℕ) (hk : k > 0) : ⌊k * x⌋ < k * ⌊x⌋ + k := by
    have := by calc
      ⌊k * x⌋ ≤ k * x := by exact Int.floor_le (↑k * x)
      _ = k * (⌊x⌋ + Int.fract x) := by congr; exact Eq.symm (Int.floor_add_fract x)
      _ = k * ⌊x⌋ + k * Int.fract x := by ring
      _ < k * ⌊x⌋ + k * 1 := by
        gcongr; exact Int.fract_lt_one x
      _ = k * ⌊x⌋ + k := by norm_num
    exact_mod_cast this

  -- now utilize last two facts for 2, 4, 8, 16, 32
  have : 2 * ⌊x⌋ ≤ ⌊2 * x⌋ ∧ ⌊2 * x⌋ < 2 * ⌊x⌋ + 2 := by
    constructor
    . exact_mod_cast aux₁ 2
    . exact_mod_cast aux₂ 2 (by simp)

  have : 4 * ⌊x⌋ ≤ ⌊4 * x⌋ ∧ ⌊4 * x⌋ < 4 * ⌊x⌋ + 4 := by
    constructor
    . exact_mod_cast aux₁ 4
    . exact_mod_cast aux₂ 4 (by simp)

  have : 8 * ⌊x⌋ ≤ ⌊8 * x⌋ ∧ ⌊8 * x⌋ < 8 * ⌊x⌋ + 8 := by
    constructor
    . exact_mod_cast aux₁ 8
    . exact_mod_cast aux₂ 8 (by simp)

  have : 16 * ⌊x⌋ ≤ ⌊16 * x⌋ ∧ ⌊16 * x⌋ < 16 * ⌊x⌋ + 16 := by
    constructor
    . exact_mod_cast aux₁ 16
    . exact_mod_cast aux₂ 16 (by simp)

  have : 32 * ⌊x⌋ ≤ ⌊32 * x⌋ ∧ ⌊32 * x⌋ < 32 * ⌊x⌋ + 32 := by
    constructor
    . exact_mod_cast aux₁ 32
    . exact_mod_cast aux₂ 32 (by simp)

  -- the last inequaltiies prove  63 * ⌊x⌋ ≤ 12345 < 63 * ⌊x⌋ + 63 which is not possible
  have : 63 * ⌊x⌋ ≤ 12345 := by linarith
  have : 12345 < 63 * ⌊x⌋ + 63  := by linarith
  omega