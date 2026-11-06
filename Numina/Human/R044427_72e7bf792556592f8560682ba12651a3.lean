import Mathlib

/- ## 3. Prove that the equation

$$
(x-y)^{3}+(y-z)^{3}+(z-x)^{3}=30
$$

has no solution in the set of integers. -/
theorem number_theory_223696 (x y z : ℤ) :
    (x - y)^3 + (y - z)^3 + (z - x)^3 ≠ 30 := by
  -- set a = x-y, b = y-z, then z-x = -a-b
  set a := x - y with ha
  set b := y - z with hb
  have : -a-b = z - x := by linarith
  rw [← this]
  -- then equation becomes -3*a*b*(a+b) = 30
  convert_to -3*a*b*(a+b) ≠ 30
  . ring
  -- now prove by contradiction, assume a * b * (a+b) = -10
  by_contra h
  have : a * b * (a + b) = -10 := by linarith
  -- this means a.natAbs * b.natAbs * (a+b).natAbs = 10
  have h : |a| * |b| * |a+b| = 10 := by calc
    |a| * |b| * |a+b| = |a * b * (a+b)| := by simp [abs_mul]
    _ = 10 := by rw [this]; norm_num
  repeat rw [Int.abs_eq_natAbs] at h
  norm_cast at h
  clear * - h
  -- this means a.natAbs and b.natAbs are divisors of 10
  have ha : a.natAbs ∣ 10 := by use b.natAbs * (a+b).natAbs, by rw [← h]; ring
  have hb : b.natAbs ∣ 10 := by use a.natAbs * (a+b).natAbs, by rw [← h]; ring

  -- so a, b belong to 1, 2, 5, 10 upto negation
  have h10 : (10).divisors = {1, 2, 5, 10} := by rfl
  have ha : a.natAbs ∈ (10).divisors := by simp [ha]
  rw [h10] at ha; simp at ha
  have hb : b.natAbs ∈ (10).divisors := by simp [hb]
  rw [h10] at hb; simp at hb
  -- now just do casework to show all cases are impossible for a.natAbs * b.natAbs * (a+b).natAbs = 10
  obtain ha | ha | ha | ha := ha <;> obtain ha | ha := Int.natAbs_eq_iff.mp ha
  all_goals (
    rw [ha] at h
    obtain hb | hb | hb | hb := hb <;> obtain hb | hb := Int.natAbs_eq_iff.mp hb
    all_goals (
      rw [hb] at h
      norm_num at h
    )
  )