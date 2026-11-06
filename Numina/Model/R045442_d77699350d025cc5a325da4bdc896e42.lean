import Mathlib

theorem number_theory_326868 :
    Set.ncard {p : ℤ × ℤ | (|p.1| - 2)^2 + (|p.2| - 2)^2 < 5} = 48 := by
  have h1 : {p : ℤ × ℤ | (|p.1| - 2)^2 + (|p.2| - 2)^2 < 5} = Finset.filter (fun p : ℤ × ℤ => (|p.1| - 2)^2 + (|p.2| - 2)^2 < 5) (Finset.Icc (-4 : ℤ) 4 ×ˢ Finset.Icc (-4 : ℤ) 4) := by
    ext ⟨x, y⟩
    simp
    intro h
    have h2 : x ≤ 4 := by
      cases' abs_cases x with hx hx
      · nlinarith [show (|x| - 2 : ℤ)^2 < 5 by nlinarith, h]
      · nlinarith [show (|x| - 2 : ℤ)^2 < 5 by nlinarith, h]
    have h3 : x ≥ -4 := by
      cases' abs_cases x with hx hx
      · nlinarith [show (|x| - 2 : ℤ)^2 < 5 by nlinarith, h]
      · nlinarith [show (|x| - 2 : ℤ)^2 < 5 by nlinarith, h]
    have h4 : y ≤ 4 := by
      cases' abs_cases y with hy hy
      · nlinarith [show (|y| - 2 : ℤ)^2 < 5 by nlinarith, h]
      · nlinarith [show (|y| - 2 : ℤ)^2 < 5 by nlinarith, h]
    have h5 : y ≥ -4 := by
      cases' abs_cases y with hy hy
      · nlinarith [show (|y| - 2 : ℤ)^2 < 5 by nlinarith, h]
      · nlinarith [show (|y| - 2 : ℤ)^2 < 5 by nlinarith, h]
    tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide