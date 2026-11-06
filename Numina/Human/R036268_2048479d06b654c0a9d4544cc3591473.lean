import Mathlib

/- Find all the integer solutions of the equation
$$
9 x^{2} y^{2}+9 x y^{2}+6 x^{2} y+18 x y+x^{2}+2 y^{2}+5 x+7 y+6=0
$$ -/
theorem number_theory_604225{x y: ℤ}:
  (9*x^2*y^2+9*x*y^2+6*x^2*y+18*x*y+x^2+2*y^2+5*x+7*y+6 = 0) ↔
  ((x=-2 ∧ y=0) ∨ (x=-3 ∧ y=0) ∨ (x=0 ∧ y=-2) ∨ (x=-1 ∧ y=2)) := by
  -- simplify the given equation
  have h1: (9*x^2*y^2+9*x*y^2+6*x^2*y+18*x*y+x^2+2*y^2+5*x+7*y+6 = 0) ↔
    (3*y+1)^2*(x^2+x) + 4*(3*y+1)*x + (2*y^2+7*y+6) = 0 := by
    constructor <;> intro h
    all_goals
      rw [← h]; ring
  -- if the given equation holds, 3y+1 must divide 35
  have h2: (3*y+1)^2*(x^2+x) + 4*(3*y+1)*x + (2*y^2+7*y+6) = 0 →
    3*y+1 ∣ 35 := by
    intro heq
    -- this is because, from given equation, 3y+1 must divide 2y^2+7y+6
    have hh1: 3*y+1 ∣ 2*y^2+7*y+6 := by
      use (-((3*y+1)*(x^2+x) + 4*x))
      nlinarith [heq]
    -- therefore it divide 9(2y^2+7y+6) = (3y+1)(2(3y+1)+17) + 35
    have hh2: 3*y+1 ∣ (3*y+1)*(2*(3*y+1)+17) + 35 := by
      have: (3*y+1)*(2*(3*y+1)+17) + 35 = 9*(2*y^2+7*y+6) := by ring
      rw [this]
      exact Dvd.dvd.mul_left hh1 9
    rw [← Int.dvd_iff_dvd_of_dvd_add hh2]
    apply Int.dvd_mul_right _ _
  -- therefore we solve y = 0,-2,2,-12
  have h3(h: 3*y+1 ∣ 35): y = 0 ∨ y = -2 ∨ y = 2 ∨ y = -12 := by
    -- 3y+1 ∣ 35, so |3y+1| ≤ 35
    have hh1 := Int.natAbs_le_of_dvd_ne_zero h (by norm_num)
    -- factors of 35 are 1,5,7,35
    have hh2: ∀n:ℕ, n ≤ 35 → n ∣ 35 → n = 1 ∨ n = 5 ∨
      n = 7 ∨ n = 35 := by decide
    -- therefore |3y+1| = 1,5,7,35
    have hh3 := hh2 (3*y+1).natAbs hh1 (Int.ofNat_dvd_right.mp h)
    -- solve y = 0,-2,2,-12
    rcases hh3 with heq | heq | heq | heq
    all_goals omega
  -- back to the problem
  rw [h1]; constructor <;> intro h
  · replace h3 := h3 (h2 h)
    -- given y = 0,-2,2,-12, we can solve x by substitute y
    -- into equation given by h.
    rcases h3 with hy | hy | hy | hy
    all_goals simp [hy] at h
    · -- when y = 0, x^2+x+4x+6 = 0. we solve x=-2 or -3
      have heq: (x+2)*(x+3) = 0 := by
        rw [← h]; ring
      rcases (mul_eq_zero.mp heq) with hx | hx
      all_goals replace hx := eq_neg_of_add_eq_zero_left hx
      all_goals simp [hy, hx]
    · -- when y=-2, 25(x^2+x)-20x=0, only integer solution is x=0
      have heq: x*(25*x+5) = 0 := by
        rw [← h]; ring
      rcases (mul_eq_zero.mp heq) with hx1 | hx2
      · simp [hy, hx1]
      · -- 25x+5=0, x cannnot be integer.
        omega
    · -- when y=2, 49(x^2+x)+28x+28=0, no integer solution
      have heq: 7*(7*(x*x)+11*x+4) = 0 := by
        rw [← h]; ring
      simp at heq
      have: (7:ℤ) ≠ 0 := by norm_num
      rw [quadratic_eq_zero_iff_discrim_eq_sq this] at heq
      simp at heq
      have hdis: discrim (7:ℤ) 11 4 = 3^2 := by
        simp [discrim]
      -- no integer solution for 3 = |14x+11|
      rw [hdis, sq_eq_sq_iff_eq_or_eq_neg] at heq
      omega
    · -- y = -12, 1225x^2+1085x+210=0, no integer solution
      have heq: 1225*x^2+1085*x+210 = 0 := by
        rw [← h]; ring
      replace heq: 245*(x*x) + 217*x + 42 = 0 := by
        have: 1225*x^2 + 1085*x+210 = 5 *
          (245*(x*x)+217*x+42) := by ring
        rw [this] at heq; simp at heq; simp [heq]
      have: (245:ℤ) ≠ 0 := by norm_num
      have hdis: discrim (245:ℤ) 217 42 = 77 * 77 := by
        simp [discrim]
      rw [quadratic_eq_zero_iff_discrim_eq_sq this] at heq
      simp at heq; rw [hdis] at heq
      -- 77^2 = (490x+217)^2 has no integer solution for x.
      rw [← pow_two, sq_eq_sq_iff_eq_or_eq_neg] at heq
      omega
  · -- verify the given solutions satisfy the equation
    rcases h with hxy | hxy | hxy | hxy
    all_goals simp [hxy]