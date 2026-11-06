import Mathlib

/-The solutions to the equation $x^2 - 3|x| - 2 = 0$ are.-/
theorem algebra_9215 (x : ℝ) : (x^2 - 3 * abs x - 2 = 0) ↔
    (x = (-3 - Real.sqrt 17) / 2) ∨ (x = (3 + Real.sqrt 17) / 2) := by
  -- divide the problem into solving for $x$ and checking they are solutions
  constructor
  intro hx
  -- we may see $x^2$ as $|x|^2$, and in this way we can solve for $|x|$
  have : x ^ 2 = (abs x) ^ 2 := Eq.symm (sq_abs x)
  rw [this] at hx
  have : (|x| - ((3 + Real.sqrt 17) / 2)) * (|x| - ((3 - Real.sqrt 17) / 2)) = |x| ^ 2 - 3 * |x| - 2 := by
    ring_nf
    have : √17 ^ 2 * (-1 / 4) = - 17 / 4 := by norm_num
    rw [this]; ring
  rw [hx] at this
  have : (|x| = ((3 + Real.sqrt 17) / 2)) ∨ (|x| = ((3 - Real.sqrt 17) / 2)) := by
    by_contra p
    push_neg at p
    rcases p with ⟨p₁, p₂⟩
    have q₁: (|x| - ((3 + Real.sqrt 17) / 2)) ≠ 0 := sub_ne_zero_of_ne p₁
    have q₂: (|x| - ((3 - Real.sqrt 17) / 2)) ≠ 0 := sub_ne_zero_of_ne p₂
    have : (|x| - ((3 + Real.sqrt 17) / 2)) * (|x| - ((3 - Real.sqrt 17) / 2)) ≠ 0 := mul_ne_zero q₁ q₂
    contradiction
  -- solving the equation we get two possible $|x|$, and we check that there are two $x$ affiliated to the positive root
  rcases this with pos | neg
  have : x = ((3 + Real.sqrt 17) / 2) ∨ x = - ((3 + Real.sqrt 17) / 2) := eq_or_eq_neg_of_abs_eq pos
  rcases this with pos | neg
  right; exact pos
  -- however, $|x|>0$, so we must drop the other solution
  left; rw [neg]; ring
  have : (3 - Real.sqrt 17) / 2 < 0 := by
    have : Real.sqrt 17 > 3 := by refine (Real.lt_sqrt ?hx).mpr ?_ <;> norm_num
    linarith
  rw [← neg] at this; absurd this; refine not_lt.mpr ?inr.a; exact abs_nonneg x
  -- next we chack the two $x$ are indeed solutions, which is a quick check of numbers
  intro l; rcases l with l₁ | l₂
  rw [l₁]
  -- calculate the square of $x$
  have dvd: ((-3 - √17) / 2) ^ 2 = (- 3 - Real.sqrt 17) ^ 2 / 4 := by ring
  have : (- 3 - Real.sqrt 17) ^ 2 = (-3) ^ 2 + (-Real.sqrt 17) ^ 2 + 2 * (-3) * (-Real.sqrt 17) := by ring
  have : (-3 - √17) ^ 2 = 26 - 6 * -√17 := by
    rw [this]; ring_nf
    have sq: (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
    rw [sq]; ring
  rw [dvd, this]; simp only [mul_neg, sub_neg_eq_add]
  have : (-3 - √17) / 2 < 0 := by
    have : - 3 < 0 := by norm_num
    have : - Real.sqrt 17 < 0 := by norm_num
    linarith
  -- since $x$ is negative, $|x| = -x$.
  have : |(-3 - √17) / 2| = - ((-3 - √17) / 2) := abs_of_neg this
  -- plug in the afore calculations to get the desired results
  rw [this]; ring
  rw [l₂]
  -- calculate the square of $x$
  have dvd: ((3 + √17) / 2) ^ 2 = (3 + Real.sqrt 17) ^ 2 / 4 := by ring
  have : (3 + Real.sqrt 17) ^ 2 = 3 ^ 2 + (Real.sqrt 17) ^ 2 + 2 * 3 * (Real.sqrt 17) := by ring
  have : (3 + √17) ^ 2 = 26 + 6 * √17 := by
    rw [this]; ring_nf
    have sq: (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
    rw [sq]; ring
  rw [dvd, this]
  have : (3 + √17) / 2 > 0 := by
    have : 3 > 0 := by norm_num
    have : Real.sqrt 17 > 0 := by norm_num
    linarith
  -- since $x$ is positive, $|x| = x$.
  have : |(3 + √17) / 2| = (3 + √17) / 2 := abs_of_pos this
  -- plug in the afore calculations to get the desired results
  rw [this]; ring