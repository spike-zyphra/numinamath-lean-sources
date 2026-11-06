import Mathlib

/- gcd(a,b) = gcd(a,a+b) -/
lemma gcd_add (a b : ℤ) : a.gcd b = a.gcd (a + b) := by
  by_cases ha : a = 0
  · simp [ha]
  · suffices
      {n : ℕ | 0 < n ∧ ∃ x y, n = a * x + b * y} =
      {n : ℕ | 0 < n ∧ ∃ x y, n = a * x + (a + b) * y}
    from IsLeast.unique
      (Int.gcd_least_linear ha (b := b))
      (this ▸ Int.gcd_least_linear ha (b := a + b))
    ext n
    simp only [Set.mem_setOf_eq, and_congr_right_iff]
    refine fun _ => ⟨fun ⟨x, y, h⟩ => ?_, fun ⟨x, y, h⟩ => ?_⟩
    · use x - y, y; simp [h]; ring
    · use x + y, y; simp [h]; ring

/- Given distinct integer a,b with gcd(a,b-a)=1.
  if all prime factors p of (b-a) divides n,
  then (nk+a) and (nk+b) are coprime. -/
lemma coprime_diff
    (n k a b : ℤ) (ne : a ≠ b) (h : a.gcd (b - a) = 1)
    (h' : (b - a).natAbs.primeFactorsList.all fun p => p ∣ n.natAbs) :
    IsCoprime (n * k + a) (n * k + b) := by
  simp only [List.all_eq_true, Nat.mem_primeFactorsList', ne_eq, Int.natAbs_eq_zero,
    decide_eq_true_eq, and_imp] at h'
  rw [Int.isCoprime_iff_gcd_eq_one, show n * k + b = n * k + a + (b - a) by simp,
    ← gcd_add, ← Int.isCoprime_iff_gcd_eq_one, Int.coprime_iff_nat_coprime]
  apply Nat.coprime_of_dvd
  intro p hp dvd dvd'
  specialize h' p hp dvd' (by omega)
  rw [← Int.natAbs_cast p, Int.natAbs_dvd_natAbs] at dvd dvd' h'
  rw [Int.dvd_add_right (Int.dvd_trans h' (Int.dvd_mul_right _ _))] at dvd
  have := h ▸ Int.dvd_gcd dvd dvd'
  simp only [Nat.cast_one, ← Int.natAbs_dvd_natAbs, Int.natAbs_ofNat, isUnit_one,
    Int.natAbs_of_isUnit, Nat.dvd_one] at this
  rw [this] at hp
  absurd hp
  decide

/- Supose `l` is a list of integers. Every pair of distinct integers in `l` satifies the requirement of `coprime_diff`.
  Then for every pair of distinct integers `(a,b)` in `l`, `nk+a` and `nk+b` are coprime. -/
lemma coprime_diff'
    (n k : ℤ) (l : List ℤ)
    (ne : l.Pairwise fun a b => a ≠ b)
    (h : l.Pairwise fun a b => a.gcd (b - a) = 1)
    (h' : l.Pairwise fun a b =>
      (b - a).natAbs.primeFactorsList.all fun p => p ∣ n.natAbs) :
    (l.map (fun i => n * k + i)).Pairwise IsCoprime := by
  rw [List.pairwise_iff_getElem] at ne h h' ⊢
  intro i j hi hj lt
  simp only [List.getElem_map]
  simp only [List.length_map] at hi hj
  exact coprime_diff n k l[i] l[j] (ne i j hi hj lt) (h i j hi hj lt) (h' i j hi hj lt)

/- Show that if \( k \) is an integer, then the six integers
  \( 6k - 1, 6k + 1, 6k + 2, 6k + 3, 6k + 5 \) are pairwise relatively prime. -/
theorem number_theory_4525 (k : ℤ) :
    [6 * k - 1, 6 * k + 1, 6 * k + 2, 6 * k + 3, 6 * k + 5].Pairwise IsCoprime := by
  apply coprime_diff' 6 k [-1, 1, 2, 3, 5] <;> native_decide
