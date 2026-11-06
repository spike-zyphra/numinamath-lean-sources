import Mathlib

/- The greatest common divisor of a list. -/
def List.gcd (l : List ℤ) := l.toFinset.gcd id

theorem number_theory_4523 {c : ℤ} (hc : c > 0) (l : List ℤ) :
    (l.map (c * ·)).gcd = c * l.gcd := by
  simp only [List.gcd, List.toFinset, ← Multiset.map_coe, Multiset.toFinset_map, Finset.gcd]
  rw [Finset.fold_image, ← Finset.gcd, ← Finset.gcd, ← List.toFinset,
    CompTriple.comp_eq, Finset.gcd_mul_left]
  -- Show `normalize c = c`
  · congr
    apply Int.normalize_of_nonneg
    linarith
  · intro x hx
    simp [hc]
    all_goals omega