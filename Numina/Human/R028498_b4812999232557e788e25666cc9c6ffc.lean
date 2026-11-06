import Mathlib.Tactic
import Mathlib.Util.Delaborators

/- A rectangular floor measures a by b feet, where a and b are positive integers with b>a. An artist paints a rectangle on the floor with the sides of the rectangle parallel to the sides of the floor. The unpainted part of the floor forms a border of width 1 foot around the painted rectangle and occupies half of the area of the entire floor. How many possibilities are there for the ordered pair (a,b)? -/

theorem AMC_Algebra_1196 (a b : Int) (area : 2*(a-2)*(b-2) - a*b = 0) (apos : a > 0) (bpos : b > 0) (hab : b > a) : (a = 5 ∧ b = 12) ∨ (a = 6 ∧ b = 8) := by
  -- The relation between the area of the painted rectangle and the area of the floor gives us the following factorization
  have : (a-4)*(b-4) = 8 := by linarith
  -- We deduce that a-4 divides 8
  have divisibility : a-4 ∣ 8 := by
    exact Dvd.intro (b - 4) this
  -- Since a-4 divides 8, a must be less than 12
  have cases_a : a ≤ 12 := by
    apply Int.le_of_mul_le_mul_left
    · linarith
    · linarith
  -- We check the possible values of a
  interval_cases a
  · contradiction
  · linarith
  · linarith
  · contradiction
  · left
    exact ⟨by rfl, by linarith⟩
  · right
    exact ⟨by rfl, by linarith⟩
  · contradiction
  · linarith
  · contradiction
  · linarith
  · contradiction
  · linarith