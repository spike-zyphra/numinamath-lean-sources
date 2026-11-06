import Mathlib

/- The greatest common divisor of a list. -/
def List.gcd (l : List ℤ) := l.toFinset.gcd id

/- Show that if \( a_{1}, a_{2}, \ldots, a_{n} \) are integers that are not all zero and \( c \) is a positive integer,
  then the greatest common divisor of the integers \( (c a_{1}, c a_{2}, \ldots, c a_{n}) \) is equal to
  \( c \) times the greatest common divisor of the integers \( (a_{1}, a_{2}, \ldots, a_{n}) \). -/
theorem number_theory_4523 {c : ℤ} (hc : c > 0) (l : List ℤ) :
    (l.map (c * ·)).gcd = c * l.gcd := by
  -- To prove the goal, we need some list manipulation.
  simp only [List.gcd, List.toFinset, ← Multiset.map_coe, Multiset.toFinset_map, Finset.gcd]
  rw [Finset.fold_image, ← Finset.gcd, ← Finset.gcd, ← List.toFinset,
    CompTriple.comp_eq, Finset.gcd_mul_left]
  -- Show `normalize c = c`
  · congr
    apply Int.normalize_of_nonneg
    linarith
  -- Show for all x,y in `l`, if cx=cy then x=y.
  · simp only [List.toFinset_coe, List.mem_toFinset, mul_eq_mul_left_iff]
    intro x _ y _ h
    omega
