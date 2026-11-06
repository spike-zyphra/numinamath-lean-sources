import Mathlib

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

theorem number_theory_4525 (k : ℤ) :
    [6 * k - 1, 6 * k + 1, 6 * k + 2, 6 * k + 3, 6 * k + 5].Pairwise IsCoprime := by
  apply coprime_diff' (n := (6 : ℤ)) (k := k) (l := [-1, 1, 2, 3, 5])
  · -- Verify $l = [-1, 1, 2, 3, 5]$ is pairwise distinct.
    native_decide
  · -- Verify for any $a, b \in l$ with $a \neq b$, $\gcd(a, b - a) = 1$.
    native_decide
  · -- Verify for any $a, b \in l$ with $a \neq b$, all prime factors of $|b - a|$ divide $|6|$.
    native_decide