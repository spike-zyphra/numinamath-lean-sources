import Mathlib

lemma mod_even_add
  (a b : ℤ)
  (h : a % 2 = b % 2)
  : Even (a + b) :=
by
  rcases em (Even a) with (H|H)
  . have : Even b := by
      have : a % 2 = 0 := by exact Int.even_iff.mp H
      have : b % 2 = 0 := by omega
      exact Int.even_iff.mpr this
    exact Even.add H this
  . simp at H
    have : Odd b  := by
      have : a % 2 = 1 := by exact Int.odd_iff.mp H
      have : b % 2 = 1 := by omega
      exact Int.odd_iff.mpr this
    exact Odd.add_odd H this

lemma mod_even_sub
  (a b : ℤ)
  (h : a % 2 = b % 2)
  : Even (a - b) :=
by
  rcases em (Even a) with (H|H)
  . have : Even b := by
      have : a % 2 = 0 := by exact Int.even_iff.mp H
      have : b % 2 = 0 := by omega
      exact Int.even_iff.mpr this
    exact Even.sub H this
  . simp at H
    have : Odd b  := by
      have : a % 2 = 1 := by exact Int.odd_iff.mp H
      have : b % 2 = 1 := by omega
      exact Int.odd_iff.mpr this
    exact Odd.sub_odd H this

/- Let $A$ and $B$ be distinct positive integers of the same parity. Find positive integers $(n, m)$ such that $n^2+m^2=(A^2+B^2)/2$. Show that one such pair $(n,m)$ is $(((A+B)/2, |A-B|/2))$. -/
theorem number_theory_636254 (A B : ℤ) (hA : 0 < A) (hB : 0 < B)
    (hAB : A ≠ B) (hA' : A % 2 = B % 2) :
    ∃ n m : ℤ, 0 < n ∧ 0 < m ∧ n ^ 2 + m ^ 2 = (A ^ 2 + B ^ 2) / 2 ∧
    ((n, m) = ((A + B) / 2, |A - B| / 2) ∨ (n, m) = ((A + B) / 2, -( |A - B| / 2))) :=
by
  use (A + B) / 2, |A - B| / 2
  simp
  constructor
  . omega
  constructor
  . have : (A - B) % 2 = 0 := by
      rw [Int.sub_emod]
      rw [hA']
      simp
    have : |A - B| ≥ 2 := by
      rcases em (A > B) with (h|h)
      . have : |A - B| = A - B := by
          simp[abs]
          omega
        rw [this]
        omega
      . have : |A - B| = B - A := by
          simp[abs]
          omega
        rw [this]
        omega
    omega
  . qify
    repeat rw [Int.cast_div]
    push_cast
    field_simp
    ring_nf
    have : A ^ 2 % 2 = B ^ 2 % 2 := by
      simp [←Int.pow_eq, Int.pow]
      rw [Int.mul_emod, Int.mul_emod B]
      rw [hA']
    have : Even (A ^ 2 + B ^ 2) := by
      apply mod_even_add
      assumption
    exact even_iff_two_dvd.mp this
    simp
    simp
    apply even_iff_two_dvd.mp
    apply mod_even_sub
    assumption
    simp
    apply even_iff_two_dvd.mp
    apply mod_even_add
    assumption
    simp
