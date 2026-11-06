import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_290902 :
  {(x, y) : ℤ × ℤ | |x| + |y| < 1000}.ncard = 1998001 := by
  have : {(x, y) : ℤ × ℤ | |x| + |y| < 1000} = Finset.filter (fun p : ℤ × ℤ => |p.1| + |p.2| < 1000) (Finset.Icc (-999 : ℤ) 999 ×ˢ Finset.Icc (-999 : ℤ) 999) := by
    ext ⟨x, y⟩
    simp
    intro h
    have h1 : x ≤ 999 := by 
      cases' abs_cases x with hx hx
      · -- Case x ≥ 0
        cases' abs_cases y with hy hy
        · linarith
        · linarith
      · -- Case x < 0
        cases' abs_cases y with hy hy
        · linarith
        · linarith
    have h2 : x ≥ -999 := by 
      cases' abs_cases x with hx hx
      · -- Case x ≥ 0
        cases' abs_cases y with hy hy
        · linarith
        · linarith
      · -- Case x < 0
        cases' abs_cases y with hy hy
        · linarith
        · linarith
    have h3 : y ≤ 999 := by 
      cases' abs_cases x with hx hx
      · -- Case x ≥ 0
        cases' abs_cases y with hy hy
        · linarith
        · linarith
      · -- Case x < 0
        cases' abs_cases y with hy hy
        · linarith
        · linarith
    have h4 : y ≥ -999 := by 
      cases' abs_cases x with hx hx
      · -- Case x ≥ 0
        cases' abs_cases y with hy hy
        · linarith
        · linarith
      · -- Case x < 0
        cases' abs_cases y with hy hy
        · linarith
        · linarith
    tauto
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide