import Mathlib

theorem algebra_2840 {m : ℤ} (hm : m = 2006^2 + 2006^2 * 2007^2 + 2007^2) :
    IsSquare m ∧ Odd m := by
  have h1 : m = (2006^2 + 2006 + 1)^2 := by
    rw [hm]
    norm_num
  have h2 : IsSquare m := by
    rw [h1]
    exact ⟨2006^2 + 2006 + 1, by ring⟩
  have h3 : Odd m := by
    rw [h1]
    apply Odd.pow
    have h4 : Odd (2006^2 + 2006 + 1 : ℤ) := by
      use (2006^2 + 2006) / 2
      norm_num
      <;> omega
    exact h4
  constructor
  · exact h2
  · exact h3