import Mathlib

variable (n : ℤ)

/- n can factor into a*b -/
abbrev is_factor (a b : ℤ) : Prop :=
  a > 0 ∧ b > 0 ∧ a * b = n

/- n can be expressed as x^2-y^2 -/
abbrev is_diff_of_squares (x y : ℤ) : Prop :=
  x ^ 2 - y ^ 2 = n

/- factor to diff_of_squares -/
abbrev f_4600 (p : ℤ × ℤ) : ℤ × ℤ :=
  ((p.1 + p.2) / 2, (p.1 - p.2) / 2)

/- diff_of_squares to factor -/
abbrev g1 (q : ℤ × ℤ) : ℤ × ℤ :=
  (q.1 + q.2, q.1 - q.2)

/-
Show that if $ n $ is an odd positive integer, then there exists a one-to-one correspondence between the factorizations of $ n $ into two positive integers and the representations of $ n $ as the difference of two squares.
-/
theorem number_theory_4600 (hn : Odd n) :
    (∀ a b : ℤ, is_factor n a b → g1 (f_4600 (a, b)) = (a, b)) ∧
    (∀ x y : ℤ, is_diff_of_squares n x y → f_4600 (g1 (x, y)) = (x, y)) := by

  constructor

  -- (∀ a b : ℤ, is_factor n a b → g (f (a, b)) = (a, b))
  . rintro a b ⟨_, ⟨_, hab⟩⟩
    obtain ⟨⟨ka, hka⟩, ⟨kb, hkb⟩⟩ := Int.odd_mul.mp (show Odd (a * b) by simp [hab, hn])
    simp only [g1]
    ext <;> omega

  -- (∀ x y : ℤ, is_diff_of_squares n x y → f (g (x, y)) = (x, y))
  . rintro x y hxy
    rw [is_diff_of_squares] at hxy
    simp only [g1, f_4600]
    ext <;> omega
