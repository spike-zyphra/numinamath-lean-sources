import Mathlib
/-- 12.55 Find the integer solutions of the equation $\frac{x y}{z}+\frac{x z}{y}+\frac{y z}{x}=3$.
    (26th Moscow Mathematical Olympiad, 1963) -/
theorem algebra_202287 (x y z : ℤ) (h : x ≠ 0) (h' : y ≠ 0) (h'' : z ≠ 0)
    (h''' : x * y / (z : ℚ) + x * z / y + y * z / x = 3) :
    (x, y, z) = (1, 1, 1) ∨ (x, y, z) = (1, -1, -1) ∨ (x, y, z) = (-1, 1, -1) ∨
    (x, y, z) = (-1, -1, 1) := by

  let p x y z := x * y / (z : ℚ) + x * z / y + y * z / x = 3
  -- First we find the positive integer solutions of the given equation (x0,y0,z0).
  have full_pos_case (x y z : ℤ) (h : 1 ≤ x) (h' : 1 ≤ y) (h'' : 1 ≤ z) (h''' : p x y z) : (x,y,z) = (1,1,1) := by
    -- The given equation can be transformed into x^2 y^2 + x^2 z^2 + y^2 z^2 = 3xyz.
    have : x^2 * y^2 + x^2 * z^2 + y ^2 * z^2 = 3 * x * y * z := by
      qify
      rw[← h''']
      field_simp
      ring
    -- Then, 6xyz
    have ineq (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) : 2 * x * y * z * (x + y + z) ≤ 6 * x * y * z := by

      change 2 * x * y * z * (x + y + z) ≤ 2 * 3 * x * y * z
      conv => rhs; rw[mul_assoc, mul_assoc, mul_assoc]; rhs; rw[← mul_assoc, ← mul_assoc, ← this]
      -- = 2x^2 y^2 + 2x^2 z^2 + 2y^2z^2 = (x^2 y^2 + x^2 z^2) + (x^2 y^2 +y^2 z^2) + (x^2 z^2 + y^2 z^2)
      have xyxz := two_mul_le_add_pow_two (x * y) (x * z)
      have xyyz := two_mul_le_add_pow_two (x * y) (y * z)
      have xzyz := two_mul_le_add_pow_two (x * z) (y * z)
      -- >= 2 x^2 yz + 2xy^2z + 2xyz^2, since in general a^2 + b^2 >= 2ab.
      -- But that equals 2xyz(x+y+z).
      convert_to 2 * x^2 * y * z + 2 * x * y^2 * z + 2 * x * y * z^2 ≤ _
      · ring
      · linarith
    -- The considered numbers are all positive. Thus, we have x + y + z <= 3.
    have ineq' (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) : x + y + z ≤ 3 := by
      specialize ineq hx hy hz
      convert_to 2 * x * y * z * (x + y + z) ≤ 2 * x * y * z * 3 at ineq
      · ring
      · rwa[mul_le_mul_iff_of_pos_left] at ineq
        positivity
    -- If x,y,z are positive integers, we can only have x = y = z = 1.
    simp only [Prod.mk_one_one, Prod.mk_eq_one]
    omega
  -- Now consider general integer solutions.
  -- A little lemma: If x,y,z is such a solution with x < 0, y > 0, we have z < 0:
  have only_two {x y z} : p x y z → x < 0 → y > 0 → z ≤ 0 := by
    intro eq neg pos
    by_contra! hz
    unfold p at eq
    -- Otherwise, we would have a single negative term in each of the three quotients,
    -- such that every summand would be negative,
    have : ↑x * ↑y / (z : ℚ) + ↑x * ↑z / (y : ℚ) + ↑y * ↑z / (x : ℚ) < 0 := by
      qify at pos neg hz
      apply add_neg
      · apply add_neg
        · apply div_neg_of_neg_of_pos ?goal1 hz
          · apply mul_neg_of_neg_of_pos neg pos
        · apply div_neg_of_neg_of_pos ?goal2 pos
          · apply mul_neg_of_neg_of_pos neg hz
      · apply div_neg_of_pos_of_neg ?goal3 neg
        · apply mul_pos pos hz
    -- and the sum could not equal 3.
    rw[eq] at this
    contradiction
  -- We can, however, swap two signs at once, since they cancel out in every quotient.
  -- Hence, if (x,y,z) is a solution, so is (x,-y,-z),
  have mymz : p x y z → p x (-y) (-z) := by
    unfold p
    intro h
    rw[← h]
    ring
  -- as well as (-x,y,-z)
  have mxmz : p x y z → p (-x) y (-z) := by
    unfold p
    intro h
    rw[← h]
    ring
  -- and (-x,-y,z)
  have mxmy : p x y z → p (-x) (-y) z := by
    unfold p
    intro h
    rw[← h]
    ring
  -- So consider a general solution (x,y,z).
  obtain ⟨(hx|hx),(hy|hy),(hz|hz)⟩ : _ ∧ _ ∧ _ := ⟨lt_or_gt_of_ne h, lt_or_gt_of_ne h', lt_or_gt_of_ne h''⟩
  -- If x<0,y<0,z<0, then x,-y,-z would be a solution.
  · have := mymz h'''
    exfalso
    -- But by the lemma, that would imply z > 0.
    have := only_two this (by simp[hx]) (by simp[hy])
    norm_cast at this
    linarith
  -- If x<0,y<0,z>0, then
  · have := mxmy h'''
    have hx : 1 ≤ - x := by omega
    have hy : 1 ≤ - y := by omega
    have hz : 1 ≤ z := by assumption
    -- (-x,-y,z) is another solution,
    specialize full_pos_case (-x) (-y) z hx hy hz
    right; right; right
    -- hence -x = 1, -y = 1, z = 1 and
    push_cast at full_pos_case
    specialize full_pos_case this
    simp only [Prod.mk_one_one, Prod.mk_eq_one] at full_pos_case
    -- (x,y,z) = (-1,-1,1).
    simp only [Int.reduceNeg, Prod.mk.injEq]
    omega
  -- Similarly, if x<0,y>0,z<0, we have -x=1,y=1,-z=1, (x,y,z) = (-1,1,-1).
  · have := mxmz h'''
    have hx : 1 ≤ - x := by omega
    have hy : 1 ≤ y := by assumption
    have hz : 1 ≤ - z := by omega
    specialize full_pos_case (-x) y (-z) hx hy hz
    right; right; left
    push_cast at full_pos_case
    specialize full_pos_case this
    simp only [Prod.mk_one_one, Prod.mk_eq_one] at full_pos_case
    simp only [Int.reduceNeg, Prod.mk.injEq]
    omega
  -- x<0,y>0,z>0 is again impossible by the lemma.
  · specialize only_two h''' (by assumption_mod_cast) (by assumption_mod_cast)
    norm_cast at only_two
    linarith
  -- x>0,y<0,z<0 implies x=1,y=-1,z=-1 as previously.
  · have := mymz h'''
    have hx : 1 ≤ x := by assumption
    have hy : 1 ≤ - y := by omega
    have hz : 1 ≤ - z := by omega
    specialize full_pos_case x (-y) (-z) hx hy hz
    right; left;
    push_cast at full_pos_case
    specialize full_pos_case this
    simp only [Prod.mk_one_one, Prod.mk_eq_one] at full_pos_case
    simp only [Int.reduceNeg, Prod.mk.injEq]
    omega
  -- x>0, y<0, z>0 implies (-x,-y,z) is another solution, to which the lemma applies,
  -- contradictorily implying z<0.
  · have := mxmy h'''
    specialize only_two (by exact_mod_cast this) (by simp[hx]) (by simp[hy])
    norm_cast at only_two
    linarith
  -- x>0, y>0, z<0 has (-x,y,-z) is another solution, to which the lemma applies,
  -- contradicting via -z<0.
  · have := mxmz h'''
    specialize only_two (by exact_mod_cast this) (by simp[hx]) (by simp[hy])
    norm_cast at only_two
    linarith
  -- x>0,y>0,z>0 has been covered already and implies (x,y,z)=(1,1,1).
  · left
    apply full_pos_case x y z hx hy hz h'''
  -- Hence the solutions are exactly (1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1).