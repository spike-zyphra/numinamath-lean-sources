import Mathlib

/- Show that \(3^{10} \equiv 1 \mod 11^{2}\).-/
theorem number_theory_4783 : 3^10 ≡ 1 [ZMOD 11^2] := by
  -- verify by computation
  native_decide
