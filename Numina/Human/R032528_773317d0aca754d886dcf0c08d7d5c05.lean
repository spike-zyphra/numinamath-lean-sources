import Mathlib

/- Show that there are no positive integers $a$ und $b$ such that $4a(a + 1) = b(b + 3)$-/
theorem number_theory_82056 :
    ¬∃ a b : ℤ, 0 < a ∧ 0 < b ∧ 4 * a * (a + 1) = b * (b + 3) := by
  rintro ⟨a, b, ha, hb, h⟩
  -- By comparing the size of b² and a², we have b = 2a.
  have : b = 2 * a := by
    nlinarith
  -- A contradiction could be derived.
  nlinarith