import Mathlib

open Real

/- tan (x+y) = (tan x + tan y) / (1 - tan x tan y) for any x,y,
for non-singular point of tan function. -/
lemma l_tan_add_eq_of_cos_ne_zero {x y: ℝ}
  (hx: cos x ≠ 0) (hy: cos y ≠ 0):
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) := by
  apply tan_add' ?_
  constructor <;> rintro k rfl
  · absurd hx
    rw [cos_eq_zero_iff]
    use k
  · absurd hy
    rw [cos_eq_zero_iff]
    use k

/- 0 < √(x^2+1) -/
lemma l_pos_sqrt_one_add_sq (x: ℝ):
  0 < √(1 + x^2) := by
  apply sqrt_pos_of_pos ?_
  linarith only [sq_nonneg x]


/- 46. (ROM 5) If $x, y, z$ are real numbers satisfying the relations $x+y+z=1$ and $\arctan x+\arctan y+\arctan z=\pi / 4$, prove that  $$ x^{2 n+1}+y^{2 n+1}+z^{2 n+1}=1 $$  for all positive integers $n$. -/
theorem algebra_24710 {x y z : ℝ} {n : ℕ} (hn : n > 0)
  (h1 : x + y + z = 1) (h2 : arctan x + arctan y + arctan z = π / 4) :
  x^(2 * n + 1) + y^(2 * n + 1) + z^(2 * n + 1) = 1 := by

  -- let arctan x = a, arctan y = b, arctan z = c
  set a := arctan x with a_def
  set b := arctan y with b_def
  set c := arctan z with c_def
  have x_of_a: x = tan a := (tan_arctan x).symm
  have y_of_b: y = tan b := (tan_arctan y).symm
  have z_of_c: z = tan c := (tan_arctan z).symm

  -- cos a, cos b, cos c ≠ 0
  have ha: cos a ≠ 0 := (cos_arctan_pos _).ne'
  have hb: cos b ≠ 0 := (cos_arctan_pos _).ne'
  have hc: cos c ≠ 0 := (cos_arctan_pos _).ne'

  -- - π < a+b < π
  have ltab: - π < a+b := by
    have hh1 := neg_pi_div_two_lt_arctan x
    have hh2 := neg_pi_div_two_lt_arctan y
    rw [a_def, b_def]
    linarith only [hh1, hh2]
  have ablt: a+b < π := by
    have hh1 := arctan_lt_pi_div_two x
    have hh2 := arctan_lt_pi_div_two y
    rw [a_def, b_def]
    linarith only [hh1, hh2]

  -- 2n+1 is odd
  have hodd: Odd (2*n+1) := by
    refine Even.add_one ?_
    exact even_two_mul n

  -- cases on whether cos (a+b) = 0
  -- if it = 0, we find c is -π/4
  -- and z = -1, x = y = 1.
  by_cases hab: cos (a+b) = 0
  · have: a + b = π / 2 := by
      rw [cos_eq_zero_iff] at hab
      rcases hab with ⟨k, hk⟩
      replace ltab: (2*k + 3: ℝ) * π > 0 := by
        rw [hk] at ltab
        linarith only [ltab]
      replace ablt: (2*k-1: ℝ) * π < 0 := by
        rw [hk] at ablt
        linarith only [ablt]
      replace ltab: 2*k+3 > (0:ℝ) :=
        (pos_iff_pos_of_mul_pos ltab).mpr pi_pos
      replace ablt: 2*k-1 < (0:ℝ) :=
        (neg_iff_pos_of_mul_neg ablt).mpr pi_pos
      norm_cast at ltab ablt
      obtain (rfl | rfl): k = 0 ∨ k = -1 := by omega
      · simp [hk]
      · have hh: c = (3/4) * π := by
          rw [hk] at h2
          norm_num at h2
          linarith only [h2]
        have := arctan_lt_pi_div_two z
        rw [← c_def, hh] at this
        linarith only [this, pi_pos]
    -- then c = - π/4, z = -1.
    have ceq: c = - (π / 4) := by
      rw [this] at h2
      linarith only [h2]
    have zeq: z = -1 := by
      rw [z_of_c, ceq, tan_neg, tan_pi_div_four]
    -- simplify cos (a+b), we find xy = 1.
    replace: cos (a+b) = (1-x*y) / (√(1+x^2) * √(1+y^2)) := by
      simp only [cos_add, a_def, b_def, cos_arctan, sin_arctan]
      ring
    -- then xy = 1.
    have hxy1: x*y = 1 := by
      symm at this
      rw [hab] at this
      have h: 0 < √(1+x^2) * √(1+y^2) := mul_pos
        (l_pos_sqrt_one_add_sq x) (l_pos_sqrt_one_add_sq y)
      simp only [div_eq_zero_iff, h.ne', or_false] at this
      linarith only [this]
    -- x + y = 2, since c = -1.
    have hxy2: x + y = 2 := by
      rw [zeq] at h1
      linarith only [h1]

    -- therefore we solve x = y = 1, done.
    have xypos: 0 < x*y := by norm_num [hxy1]
    replace xypos: 0 < x ∧ 0 < y := by
      rw [mul_pos_iff] at xypos
      refine xypos.resolve_right (fun hh => ?_)
      linarith only [hh, hxy2]
    have xeqy: x = y := by
      suffices √x = √y by
        rwa [sqrt_inj xypos.left.le xypos.right.le] at this
      suffices (√x - √y)^2 = 0 by
        rw [sq_eq_zero_iff] at this
        exact eq_of_sub_eq_zero this
      have: (√x - √y)^2 = (√x)^2 + (√y)^2 - 2 * √(x*y) := by
        rw [sqrt_mul xypos.left.le]
        ring
      rw [this, sq_sqrt xypos.left.le,
      sq_sqrt xypos.right.le, hxy2, hxy1]
      norm_num
    have xeq: x = 1 := by linarith only [xeqy, hxy2]
    have yeq: y = 1 := by linarith only [xeqy, hxy2]
    simp [xeq, yeq, zeq, hodd.neg_one_pow]


  -- cases on whether sin (a+b) = 0
  -- if sin (a+b) = 0, we find a+b is 0, and solve c = 1, x = -y.
  by_cases hab': sin (a+b) = 0
  · rw [sin_eq_zero_iff_of_lt_of_lt ltab ablt] at hab'
    rw [hab', zero_add] at h2
    rw [h2, tan_pi_div_four] at z_of_c
    have x_eq_negy: x = -y := by
      rw [z_of_c] at h1
      linarith only [h1]
    rw [x_eq_negy, hodd.neg_pow, z_of_c]
    simp


  -- now cos (a+b), sin(a+b) ≠ 0, and it follows that tan (a+b) ≠ 0.
  have hhab: tan (a+b) ≠ 0 := by
    rw [tan_eq_sin_div_cos]
    exact div_ne_zero hab' hab
  -- consider tan (a+b+c)
  have heq := l_tan_add_eq_of_cos_ne_zero hab hc
  -- tan (π/4) = 1 ≠ 0, so denominator ≠ 0.
  -- multiply it to left side
  replace heq: (1 - tan (a+b) * tan c) * tan (a+b+c) =
    tan (a+b) + tan c := by
    have: 1 - tan (a+b) * tan c ≠ 0 := by
      rintro hh
      simp [hh, h2, tan_pi_div_four] at heq
    field_simp [this] at heq
    linarith only [heq]
  -- expand tan (a+b), and express whole formula in terms of x,y,z.
  replace heq: (x-1) * (y-1) * (z-1) = 0 := by
    rw [l_tan_add_eq_of_cos_ne_zero ha hb] at heq
    have: 1 - tan a * tan b ≠ 0 := by
      rw [l_tan_add_eq_of_cos_ne_zero ha hb,
      ne_eq, div_eq_zero_iff] at hhab
      push_neg at hhab
      exact hhab.right
    field_simp [this] at heq
    simp only [← x_of_a, ← y_of_b, ← z_of_c,
    h2, tan_pi_div_four] at heq
    replace heq: 1 + x*y*z = (x+y+z) + x*y + x*z + y*z := by
      linarith only [heq]
    simp only [h1, add_assoc, add_right_inj] at heq
    have: (x-1) * (y-1) * (z-1) = x*y*z + (x+y+z)
      - (x*y+x*z+y*z) - 1 := by ring
    rw [this, h1]
    linarith only [heq]

  -- then one of x,y,z is 1.
  obtain (xeq | yeq | zeq): x = 1 ∨ y = 1 ∨ z = 1 := by
    simp only [mul_eq_zero] at heq
    rcases heq with heq | heq
    · rcases heq with heq | heq
      · left; linarith only [heq]
      · right; left; linarith only [heq]
    · right; right; linarith only [heq]

  · -- x = 1, y = -z, done.
    have y_of_z: y = -z := by
      rw [xeq] at h1
      linarith only [h1]
    simp [y_of_z, xeq, hodd.neg_pow]
  -- other two cases are similar.
  · have x_of_z: x = -z := by
      rw [yeq] at h1
      linarith only [h1]
    simp [x_of_z, yeq, hodd.neg_pow]
  · have x_of_y: x = -y := by
      rw [zeq] at h1
      linarith only [h1]
    simp [zeq, x_of_y, hodd.neg_pow]