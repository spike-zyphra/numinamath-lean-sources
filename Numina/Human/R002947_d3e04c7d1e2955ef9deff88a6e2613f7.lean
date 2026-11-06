import Mathlib

open Polynomial Finset

-- If p(x) = c for all x ∈ s and p.natDegree < s.card then p = c.
lemma eq_const_of_natDegree_lt_card_of_eval_eq {c : ℝ} {p : ℝ[X]} (s : Finset ℝ)
    (heval : ∀ x ∈ s, p.eval x = c) (hcard : p.natDegree < s.card) :
    p = C c := by
  -- Define q = p - C c.
  let q : ℝ[X] := p - C c
  -- It is enough to show that q = 0.
  suffices q = 0 by
    simp [q] at this
    linear_combination this
  -- If q(x) = 0 for all x ∈ s and q.natDegree < s.card then q = 0.
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' q s
  · intro x hx
    -- q(x) for all x ∈ s because q(x) = p(x) - c = c - c = 0 for x ∈ s.
    simp [q, heval x hx]
  · calc
      -- q.natDegree ≤ max p.natDegree 0 = p.natDegree < s.card.
      q.natDegree ≤ max p.natDegree (C c).natDegree := by
        apply natDegree_sub_le
      _ = max p.natDegree 0 := by
        rw [natDegree_C]
      _ = p.natDegree := by
        simp only [zero_le, sup_of_le_left]
      _ < s.card := hcard

/- 3. Find the reduced polynomial $P(x)$ (the coefficient of the highest degree of the variable is 1), for which the identity $x P(x-1)=(x-6) P(x)$ holds. -/
theorem algebra_133687 {P : Polynomial ℝ} :
    (P.Monic ∧ X * P.comp (X - C 1) = (X - C 6) * P) ↔
    P = X * (X - C 1) * (X - C 2) * (X - C 3) * (X - C 4) * (X - C 5) := by
  symm
  constructor
  · -- Assume that P = X * (X - 1) * (X - 2) * (X - 3) * (X - 4) * (X - 5) and show that
    -- x * P(x - 1) = (x - 6) * P(x) for all x ∈ ℝ.
    intro heq
    constructor
    · simp [heq]
      repeat apply Monic.mul _ (monic_X_sub_C _)
      exact monic_X
    apply Polynomial.funext
    intro x
    simp [heq]
    ring
  -- Assume that P is monic and X * P(X - 1) = (X - 6) * P.
  -- Show that P = X * (X - 1) * (X - 2) * (X - 3) * (X - 4) * (X - 5).
  intro ⟨hmono, h⟩
  have he (x : ℝ) : x * P.eval (x - 1) = (x - 6) * P.eval x := by
    apply_fun eval x at h
    simp_all
  -- We have P ≠ 0 (because P is monic).
  have hP0 := hmono.ne_zero
  -- Define s = {0, 1, ... , 5} (as Multiset ℝ).
  set s : Multiset ℝ := (Multiset.range 6).map (fun x : ℕ => (x : ℝ))
  -- Show that s ≤ P.roots.
  have hr : s ≤ P.roots := by
    -- We have x ∈ s ↔ ∃ i ∈ [0, 6), x = i.
    have hs (x : ℝ) : x ∈ s ↔ ∃ i ∈ range 6, x = i := by
      simp only [s, Multiset.mem_map, Multiset.mem_range, mem_range, Eq.comm]
    -- s has no duplicates.
    have hs_dup : s.Nodup := by
      apply Multiset.Nodup.map (by intro x y; simp)
      apply Multiset.nodup_range
    -- Since s has not duplicates, it is enough to show that s ⊆ P.roots.
    rw [Multiset.le_iff_subset hs_dup]
    -- Show that if x ∈ s then P(x) = 0.
    intro x
    rw [hs]
    intro ⟨i, hi, hx⟩
    subst x
    simp only [mem_range] at hi
    -- We have i < 6 and we need to show that P(i) = 0.
    simp
    -- Proof by induction.
    induction i with
    | zero =>
      -- P(0) * (0 - 6) = 0 * P(0 - 1), so P(0) = 0.
      simp [hP0]
      have := he 0
      simp at this
      exact this
    | succ i ih =>
      -- Consider P(i + 1), i + 1 < 6.
      simp [hP0]
      -- We have (i + 1 - 6) * P(i + 1) = (i + 1) * P(i + 1 - 1).
      -- We have i + 1 - 6 ≠ 0 and P(i + 1 - 1) = P(i) = 0, so
      -- P(i + 1) = 0.
      have := he (i + 1)
      simp [ih (by omega)] at this
      cases' this with h h
      · replace hi : i + 1 ≤ 5 := by omega
        rify at hi
        linarith
      exact h
  -- s ≤ P.roots implies that P = Q * ∏ i ∈ range 26, (X - i) for some polynomial Q.
  have ⟨Q, hPQ⟩ : ∃ Q : ℝ[X], P = Q * ∏ i ∈ range 6, (X - C (i : ℝ)) := by
    have ⟨Q, hQ⟩ := (Multiset.prod_X_sub_C_dvd_iff_le_roots hP0 s).mpr hr
    use Q
    rw [hQ, mul_comm]
    rfl
  -- Show that Q(x - 1) = Q(x) for all 6 < x.
  have hQ {x : ℝ} (hx : 6 < x) : Q.eval (x - 1) = Q.eval x := by
    -- We have x * P(x - 1) = (x - 6) * P(x) and
    -- P(x) = Q(x) * ∏ i ∈ range 6, (x - i).
    replace he := he x
    simp [hPQ, eval_prod, prod_range_succ] at he
    rw [← mul_left_inj' (c := x * (x - 1) * (x - 2) * (x - 3) * (x - 4) * (x - 5) * (x - 6))]
    · linear_combination he
    apply ne_of_gt
    repeat apply mul_pos _ (by linarith)
    linarith
  -- Show that Q = C c for some c ∈ ℝ.
  have ⟨c, hc⟩ : ∃ c, Q = C c := by
    -- Show that Q = C (Q(10)).
    use eval 10 Q
    -- It is enough to show that Q(10 + i) = Q(10) for all i ∈ [0, Q.natDegree + 1)
    -- and [0, Q.natDegree + 1).card > Q.natDegree.
    apply eq_const_of_natDegree_lt_card_of_eval_eq ((Finset.range (1 + Q.natDegree)).image (fun n : ℕ => 10 + (n : ℝ)))
    · simp only [mem_image, mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro i hi
      -- Proof by induction.
      induction i with
      -- Q(10 + 0) = Q(10).
      | zero => simp
      | succ i ih =>
        -- Q(10 + i + 1) = Q (10 + i + 1 - 1) = Q(10 + i) = Q(10) (since 10 + i > 26).
        rw [← ih (by omega), ← hQ (by linarith)]
        congr
        push_cast
        ring
    · -- [0, Q.natDegree + 1).card = Q.natDegree + 1 > Q.natDegree.
      rw [card_image_of_injective _ (by intro x y; simp)]
      simp only [card_range, lt_add_iff_pos_left, zero_lt_one]
  -- Q = C c, so P = C c * ∏ i ∈ range 6, (X - i).
  -- It is left to show that c = 1.
  suffices c = 1 by
    simp [hPQ, hc, this, prod_range_succ]
    apply Polynomial.funext
    intro x
    simp
  -- Show that the leading coefficient of P is equal to the leading coefficient of Q.
  have : P.leadingCoeff = Q.leadingCoeff := by
    simp only [hPQ, leadingCoeff_mul]
    suffices (∏ i ∈ range 6, (X - C (i : ℝ))).leadingCoeff = 1 by
      rw [this, mul_one]
    simp only [prod_range_succ, range_one, prod_singleton, CharP.cast_eq_zero,
      sub_zero, Nat.cast_ofNat, leadingCoeff_mul, monic_X, Monic.leadingCoeff,
      one_mul]
    simp only [map_zero, sub_zero, monic_X, Monic.leadingCoeff, map_one, one_mul,
      leadingCoeff_X_sub_C, mul_one]
  -- The leading coefficient of P is 1 (because P is monic),
  -- the leading coefficient of Q is c, so c = 1.
  rw [Monic] at hmono
  rw [hmono] at this
  simp [this, hc]