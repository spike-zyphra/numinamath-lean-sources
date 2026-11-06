import Mathlib

open Polynomial

set_option maxRecDepth 1000

theorem algebra_96510 (a : ℤ) (ha : a > 0) {s : Set ℤ}
    (hs : s = {c : ℤ | c > 0 ∧ ∃ x1 x2 x3 : ℤ, x1 > 0 ∧ x2 > 0 ∧ x3 > 0 ∧ (2 * X^3 - C (2 * a) * X^2 + C (a ^ 2 - 81) * X - C c : ℤ[X]).roots = {x1, x2, x3}})
    (hs2 : s.ncard = 2) :
    ∑ᶠ c ∈ s, c = 440 := by 
  suffices h : ∀ c, c ∈ s → a = 13 ∧ c = 64 ∨ a = 15 ∧ (c = 216 ∨ c = 224) by
    -- s.ncard = 2 so there exist c1 and c2 such that c1 ≠ c2 and s = {c1, c2}
    rw [Set.ncard_eq_two] at hs2
    replace ⟨c1, c2, hc, hs2⟩ := hs2
    rw [hs2, finsum_mem_eq_toFinset_sum]
    -- we have c2 ∈ s so a = 13 and c2 = 64 or a = 15 and c2 ∈ {216, 224}
    have hc2 := h c2 (by simp [hs2])
    -- we have c1 ∈ s so a = 13 and c1 = 64 or a = 15 and c1 ∈ {216, 224}
    obtain ⟨ha, hc1⟩ | ⟨ha, hc1⟩ := h c1 (by simp [hs2])
    -- suppose that a = 13 and c1 = 64
    · cases' hc2 with h2 h2
      -- this case is impossible since a = 13 implies that c2 = 64 and so c1 = c2, a contradiction
      · rw [hc1, h2.2] at hc
        contradiction
      · rw [ha] at h2
        norm_num at h2
    -- suppose that a = 15 and c1 ∈ {216, 224}
    · cases' hc2 with h2 h2
      · rw [ha] at h2
        norm_num at h2
      -- we get c2 ∈ {216, 224}, so s = {216, 224} and the sum is equal to 440
      · cases' hc1 with hc1 hc1
        · simp [hc1, show c2 = 224 by omega]
        · simp [hc1, show c2 = 216 by omega]
  -- now prove that c ∈ s implies (a, c) = (13, 64) or a = 15 and c ∈ {216, 224}
  intro c
  simp only [hs, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  intro ⟨hc, x1, x2, x3, hx1, hx2, hx3, hroots⟩
  -- x1, x2, x3 are roots of the given polynomial
  -- without loss of generality, assume that x1 ≤ x2 ≤ x3
  wlog h123 : x1 ≤ x2 ∧ x2 ≤ x3 generalizing x1 x2 x3 with h
  · set xs := ({x1, x2, x3} : Multiset ℤ).sort (fun a b => a ≤ b) with hxs
    have h3 : xs.length = 3 := by simp [xs]
    have hx {x} (hx : x ∈ xs) : 0 < x := by
      simp [xs] at hx
      omega
    have xs_eq : xs = [xs[0], xs[1], xs[2]] := by
      apply List.ext_get (by simp [h3])
      simp [h3]
      intro n hn _
      interval_cases n <;> simp
    apply h xs[0] xs[1] xs[2] <;> try (apply hx; simp)
    · rw [hroots]
      rw [←Multiset.sort_eq (fun a b => a ≤ b) {x1, x2, x3}, ←hxs]
      congr
    · have := Multiset.sort_sorted (fun a b => a ≤ b) {x1, x2, x3}
      rw [←hxs, xs_eq] at this
      simp at this
      tauto
  -- x1, x2, x3 are roots of the given polynomial
  -- let p be the polynomial from the definition of s
  set p : ℤ[X] := (2 * X^3 - _ + _ - _)
  -- the degree of p is 3
  have hp_deg : p.natDegree = 3 := by dsimp [p]; compute_degree!
  -- p has exactly 3 roots (x1, x2, x3)
  have hp_roots : p.roots.card = p.natDegree := by simp [hroots, hp_deg]
  -- the leading coefficient of p is 2
  have hp3 : p.leadingCoeff = 2 := by
    simp_rw [leadingCoeff, hp_deg, p]
    compute_degree!
  -- use Vieta's identities to show that
  -- eq1: x1 + x2 + x3 = a
  -- eq2: 2 * (x1 * x2 + x1 * x3 + x2 * x3) = a ^ 2 - 81
  -- eq3: 2 * x1 * x2 * x3 = c
  have ⟨eq1, eq2, eq3⟩ : x1 + x2 + x3 = a ∧ 2 * (x1 * x2 + x1 * x3 + x2 * x3) = (a ^ 2 - 81) ∧ 2 * x1 * x2 * x3 = c := by
    have hc0 {k} (c : ℤ) (hk : 1 ≤ k) : (c : Polynomial ℤ).coeff k = 0 := by compute_degree; omega
    constructorm* _ ∧ _
    · have hp2 : p.coeff 2 = -2 * a := by
        simp [p, hc0]
        norm_cast
        rw [hc0 _ (by norm_num), add_zero]
        simp
        compute_degree
      rw [←mul_right_inj' (show (-2 : ℤ) ≠ 0 by norm_num), ←hp2]
      rw [coeff_eq_esymm_roots_of_card hp_roots (by omega), hroots, hp3, hp_deg]
      simp [Multiset.esymm, Multiset.powersetCard_one]
      ring
    · have hp1 : p.coeff 1 = a ^ 2 - 81 := by
        simp [p, hc0]
        norm_cast
        rw [intCast_coeff_zero]
        simp
        rw [show 2 * (a : ℤ[X]) * X^2 = C (2 * a) * X^2 by simp]
        rw [coeff_C_mul_X_pow]
        simp
      rw [←hp1]
      rw [coeff_eq_esymm_roots_of_card hp_roots (by omega), hroots, hp3, hp_deg]
      simp [Multiset.esymm, Multiset.powersetCard_one]
      ring
    · have hp0 : -p.coeff 0 = c := by simp [p]
      rw [←hp0]
      rw [coeff_eq_esymm_roots_of_card hp_roots (by omega), hroots, hp3, hp_deg]
      simp [Multiset.esymm, Multiset.powersetCard_one, mul_assoc]
  -- we obtain that x1 ^ 2 + x2 ^ 2 + x3 ^ 2 = 81
  -- (this identity follows from a linear combination of eq1 and eq2)
  have eq : x1 ^ 2 + x2 ^ 2 + x3 ^ 2 = 81 := by
    nlinarith
  -- suppose w(x^2), and norm_num
  have eq' : x1 ≤ 9 := by nlinarith
  have eq' : x2 ≤ 9 := by nlinarith
  have eq' : x3 ≤ 9 := by nlinarith
  -- it is a manual work to verify that
  -- w(x1root term).two.tactics
  interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;> omega