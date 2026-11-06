import Mathlib

theorem number_theory_182811 : ∑ i ∈ Finset.Icc 1 2016, i^2017 ≡ 0 [ZMOD 2017] ∧ ¬∑ i ∈ Finset.Icc 1 2016, i^2017 ≡ 0 [ZMOD 2018] := by
  constructor
  · -- Show that $1^{2017} + 2^{2017} + \cdots + 2016^{2017} \equiv 0 \mod 2017$
    native_decide
  · -- Show that $1^{2017} + 2^{2017} + \cdots + 2016^{2017} \neq 0 \mod 2018$
    native_decide