import Mathlib

theorem number_theory_271253 : IsLeast {n | (n.divisors.card = 20)} 240 := by
  constructor
  · -- First we show that 240 belongs to the set
    native_decide
  · -- Then we show there is no smaller element in the set
    intro n hn
    by_contra h
    push_neg at h
    interval_cases n <;> try { contradiction } 