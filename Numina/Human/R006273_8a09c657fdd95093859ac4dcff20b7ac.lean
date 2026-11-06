import Mathlib

/- if ac, bc divide k, then lcm (a,b) × c also divide k.   -/
lemma l_mul_lcm_dvd_of_mul_dvd_of_mul_dvd {k a b c: ℕ}
  (hk: 0 < k) (ha: 0 < a) (hb: 0 < b) (hc: 0 < c)
  (h1: a*c ∣ k) (h2: b*c ∣ k):
  (a.lcm b) * c ∣ k := by
  have h3 := Nat.lcm_pos ha hb
  have h4: 0 < (a.lcm b) * c := mul_pos h3 hc
  rw [← Nat.factorization_prime_le_iff_dvd h4.ne' hk.ne']
  intro p pp
  rw [Nat.factorization_mul h3.ne' hc.ne',
  Nat.factorization_lcm ha.ne' hb.ne']
  by_cases hh: b.factorization p ≤ a.factorization p
  · simp only [Finsupp.coe_add, Pi.add_apply,
    Finsupp.sup_apply, hh, sup_of_le_left]
    rw [← Nat.factorization_prime_le_iff_dvd (by positivity) hk.ne',
    Nat.factorization_mul ha.ne' hc.ne'] at h1
    simpa only [ge_iff_le, Finsupp.coe_add, Pi.add_apply] using h1 p pp
  · push_neg at hh
    simp only [Finsupp.coe_add, Pi.add_apply,
    Finsupp.sup_apply, hh.le, sup_of_le_right]
    rw [← Nat.factorization_prime_le_iff_dvd (by positivity) hk.ne',
    Nat.factorization_mul hb.ne' hc.ne'] at h2
    simpa only [Finsupp.coe_add, Pi.add_apply] using h2 p pp


/- Let $V_A, V_B, V_C$ be three given positive natural numbers, corresponding to the values at the vertices of a triangle. Let $e_{AB}, e_{BC}, e_{CA}$ be positive natural numbers to be placed on the sides connecting $(V_A, V_B)$, $(V_B, V_C)$, and $(V_C, V_A)$ respectively. These numbers must be chosen such that the product of the numbers along each edge sequence (vertex-edge-vertex) is constant. That is, $V_A \cdot e_{AB} \cdot V_B = V_B \cdot e_{BC} \cdot V_C = V_C \cdot e_{CA} \cdot V_A$.
Determine the smallest possible value for $e_{AB}$. Show that this value is $V_C / \gcd(V_A, V_B, V_C)$. -/
theorem number_theory_635425 {VA VB VC: ℕ} (hA: 0 < VA) (hB: 0 < VB) (hC: 0 < VC):
  IsLeast {x:ℕ | ∃ (eAB eBC eCA: ℕ), x = eAB ∧ (0 < eAB ∧ 0 < eBC ∧ 0 < eCA) ∧
    VA * eAB * VB = VB * eBC * VC ∧ VA * eAB * VB = VC * eCA * VA}
    (VC / (VA.gcd VB).gcd VC) := by

  constructor
  · -- verification
    simp only [exists_and_left, exists_eq_left', Set.mem_setOf_eq]
    -- when eAB is VC / gcd, eBC is VA / gcd and eCA takes VB / gcd.
    use (VA / (VA.gcd VB).gcd VC), (VB / (VA.gcd VB).gcd VC)
    have h1: (VA.gcd VB).gcd VC ∣ VC := by
      exact Nat.gcd_dvd_right (VA.gcd VB) VC
    have h2: (VA.gcd VB).gcd VC ∣ VB := by
      rw [Nat.gcd_comm VA VB, Nat.gcd_assoc]
      exact Nat.gcd_dvd_left VB (VA.gcd VC)
    have h3: (VA.gcd VB).gcd VC ∣ VA := by
      rw [Nat.gcd_assoc]
      exact Nat.gcd_dvd_left VA (VB.gcd VC)
    have: 0 < (VA.gcd VB).gcd VC :=
      Nat.gcd_pos_of_pos_right (VA.gcd VB) hC
    refine ⟨?_, ?_, ?_⟩
    · split_ands
      all_goals
        apply Nat.div_pos ?_ this
        apply Nat.le_of_dvd (by assumption) (by assumption)
    all_goals
      zify at h1 h2 h3
      qify
      rw [Int.cast_div (by assumption) (by norm_cast; exact this.ne')]
      field_simp
      ring

  · -- show lower bound.
    simp only [lowerBounds, exists_and_left, exists_eq_left',
    Set.mem_setOf_eq, forall_exists_index, and_imp]
    intro eAB eBC eCA hAB hBC hCA h1 h2
    -- let K be the product.
    set K := VA * eAB * VB with h3
    have Kpos: 0 < K := by
      rw [h1]
      positivity
    -- then eAB is K / (VA VB)
    have h4: eAB = K / (VA * VB) := by
      rw [h3, mul_comm VA _, mul_assoc,
      Nat.mul_div_left _ (mul_pos hA hB)]
    -- we claim c / (gcd a b c) divide eAB
    refine Nat.le_of_dvd hAB ?_
    refine (Nat.div_dvd_iff_dvd_mul ?_ ?_).mpr ?_
    · exact Nat.gcd_dvd_right (VA.gcd VB) VC
    · refine Nat.gcd_ne_zero_right hC.ne'
    · rw [mul_comm, Nat.gcd_comm, Nat.dvd_mul_gcd_iff_dvd_mul]
      suffices (VC * (VA.lcm VB)) ∣ eAB * (VA * VB) by
        rw [← Nat.gcd_mul_lcm VA VB, ← mul_assoc] at this
        refine Nat.dvd_of_mul_dvd_mul_right ?_ this
        exact Nat.lcm_pos hA hB
      rw [← mul_assoc, mul_comm _ VA, ← h3]
      -- c (lcm a b) divide the product K
      rw [mul_comm VC _]
      apply l_mul_lcm_dvd_of_mul_dvd_of_mul_dvd Kpos hA hB hC ?_ ?_
      · rw [h2, mul_comm _ VA, ← mul_assoc]
        apply Nat.dvd_mul_right
      · rw [h1, mul_comm VB eBC, mul_assoc]
        apply Nat.dvd_mul_left