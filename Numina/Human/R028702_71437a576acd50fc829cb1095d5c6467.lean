import Mathlib

/-
Jon and Steve ride their bicycles along a path that parallels two side-by-side train tracks running the east/west direction.
Jon rides east at 20 miles per hour, and Steve rides west at 20 miles per hour.
Two trains of equal length, traveling in opposite directions at constant but different speeds each pass the two riders.
Each train takes exactly 1 minute to go past Jon.
The westbound train takes 10 times as long as the eastbound train to go past Steve.
The length of each train is m/n​ miles, where m and n are relatively prime positive integers.
Find m+n. -/
theorem algebra_95910 (r₁ r₂ : ℚ)
(hv : v = 1/3)
(h : l > 0 ∧ r₁ > v ∧ r₂ > v)
(hj₁ : 1 = l / (r₂ + v))
(hs : l / (r₂ - v) = 10 * l / (r₁ + v))
(hj₂ : l / (r₁ - v) = l / (r₂ + v))
:
∃ m n : ℕ, m > 0 ∧ n > 0 ∧ m.Coprime n ∧ l = m / n := by {
-- Let l be the length of the trains
-- Let r₁ be the speed of the faster (eastbound) train
-- let r₂ be the speed of the westbound train
-- let v be the speed of the cyclists
-- have 1 = l / (r₂ + v) and l/(r₁ - v) = l/(r₂ + v) by looking from Jon's frame of reference
-- (westbound train takes 1 minute to pass John, eastbound train takes the same time)
-- we have l/(r₂ - v) = 10 * l/(r₁ + v) by looking from Steve's frame of reference
-- (takes 10 times as long to pass Steve)

  -- the solution is 22/27
  use 22
  use 27
  constructor
  trivial
  constructor
  trivial
  constructor
  trivial

  rw [hv, div_eq_div_iff] at hj₂
  apply mul_left_cancel₀ (by linarith) at hj₂
  rw [hv, mul_comm _ l, div_eq_div_iff, mul_assoc l _] at hs
  apply mul_left_cancel₀ (by linarith) at hs

  -- Solve for r₁ in terms of r₂
  have eq₁ : r₁ = r₂ + 2/3 := by calc
    r₁ = (r₁ - 1/3) + 1/3 := by ring
    _  = r₂ + 2/3 := by rw [←hj₂]; ring
  have eq₂ : r₁ = 10 * r₂ - 11/3 := by calc
    r₁ = (r₁ + 1/3) - 1/3 := by ring
    _ = 10 * r₂ - 11/3 := by rw [hs]; ring

  -- Equate these and solve for r₂
  have r₂_def : r₂ = 13/27 := by linarith [eq₁, eq₂]

  -- Substitute back into remaining equation
  rw [hv, r₂_def] at hj₁
  norm_num at hj₁
  apply eq_of_div_eq_one
  exact id (Eq.symm hj₁)
  repeat linarith
}