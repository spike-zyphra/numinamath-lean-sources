import Mathlib

/- Pour un réel $x$, on note $\lfloor x\rfloor$ le plus grand entier relatif inférieur ou égal à $x$ (par exemple, $\lfloor 2,7\rfloor=2,\lfloor\pi\rfloor=3$ et $\lfloor-1,5\rfloor=-2$ ). On note aussi $\{x\rfloor=x-\lfloor x\rfloor$.
Trouver tous les réels $x$ tels que
$$\lfloor x\rfloor\{x\} < x-1
$$-/
theorem inequalities_607167 : {x : ℝ | ⌊x⌋ * Int.fract x < x - 1} = Set.Ici 2 := by
  ext x
  rw [Set.mem_setOf]
  -- Notice that `x=[x]+{x}`.
  nth_rw 3 [← Int.floor_add_fract x]
  constructor
  . intro hx
    -- We can simplify `[x]{x}<x-1` to `[x]{x}-[x] < {x}-1`.
    replace hx : ⌊x⌋ * Int.fract x - ⌊x⌋ * 1 < Int.fract x - 1 := by linarith
    rw [← mul_sub] at hx
    -- Simplify `[x]{x}-[x] < {x}-1` to `1-{x} < [x](1-{x})`.
    replace hx : 1 * (1 - Int.fract x) < ⌊x⌋ * (1 - Int.fract x) := by linarith
    have : Int.fract x < 1 := by exact Int.fract_lt_one x
    -- Notice that `1-{x}` is positive.
    have : 0 < 1 - Int.fract x := by linarith
    -- We have `1 < [x]`.
    rw [mul_lt_mul_iff_of_pos_right this] at hx
    norm_cast at hx
    -- Which is equivalent to `2 ≤ [x]`.
    replace hx : 2 ≤ ⌊x⌋ := by omega
    rify at hx
    rw [Set.mem_Ici]
    apply le_trans hx
    -- Hence we have `2 ≤ [x] ≤ x`.
    exact Int.floor_le x
  . -- Verify that `2≤x` is solution.
    intro hx
    -- We can simplify `[x]{x}<x-1` to `[x]{x}-[x] < {x}-1`.
    suffices ⌊x⌋ * Int.fract x - ⌊x⌋ * 1 < Int.fract x - 1 by linarith
    rw [← mul_sub]
    apply lt_of_neg_lt_neg
    -- Simplify `[x]{x}-[x] < {x}-1` to `1-{x} < [x](1-{x})`.
    rw [neg_sub, mul_comm, ← neg_mul, neg_sub]
    have : Int.fract x < 1 := by exact Int.fract_lt_one x
    -- Notice that `1-{x}` is positive.
    have : 0 < 1 - Int.fract x := by linarith
    nth_rw 1 [← mul_one (1 - _)]
    -- We have `1 < [x]`.
    gcongr
    norm_cast
    -- Which is equivalent to `2 ≤ [x]`.
    suffices 2 ≤ ⌊x⌋ by omega
    rw [show (2 : ℤ) = ⌊(2 : ℝ)⌋ by norm_num]
    apply Int.floor_le_floor
    exact hx
