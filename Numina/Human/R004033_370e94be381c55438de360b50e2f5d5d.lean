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
      _ < #s := hcard

/- Find all polynomials $P(x)$ for which the identity holds: $x P(x-1) \equiv (x-26) P(x)$.
# -/
theorem algebra_231685 {P : Polynomial ℝ} :
    (X * P.comp (X - C 1) = (X - C 26) * P) ↔
    ∃ c : ℝ, P = C c * ∏ i ∈ range 26, (X - C (i : ℝ)) := by
  -- Show that x * ∏ i ∈ range 26, (x - 1 - i) = (x - 26) * ∏ i ∈ range 26, (x - i)
  -- for all x ∈ ℝ.
  have eq (x : ℝ) : x * ∏ i ∈ range 26, (x - 1 - i) = (x - 26) * ∏ i ∈ range 26, (x - i) := calc
    -- We have x * ∏ i ∈ range 26, (x - 1 - i)
    --   = x * ∏ i ∈ range 26, (x - (1 + i))
    --   = x * Π i ∈ [1, 27), (x - i)
    --   = x * (x - 26) * ∏ i ∈ [1, 26), (x - i)
    --   = (x - 26) * ∏ i ∈ range 26, (x - i).
    _ = x * ∏ i ∈ range 26, (x - ((1 + i : ℕ) : ℝ)) := by
      congr 1
      apply prod_congr rfl
      intro i hi
      push_cast
      ring
    _ = (x - 26) * ∏ i ∈ range 26, (x - i) := by
      nth_rw 1 [show 26 = 27 - 1 by norm_num]
      rw [← prod_Ico_eq_prod_range (f := fun i : ℕ => x - i)]
      rw [prod_range_eq_mul_Ico _ (by norm_num)]
      rw [prod_Ico_succ_top (by norm_num)]
      ring
  symm
  constructor
  · intro ⟨c, heq⟩
    -- Assume that P = C c * ∏ i ∈ range 26, (X - C (i : ℝ)) and show that
    -- x * P(x - 1) = (x - 26) * P(x) for all x ∈ ℝ.
    apply Polynomial.funext
    intro x
    simp [heq, eval_prod]
    ac_nf
    rw [eq]
    ring
  -- Assume that X * P(X - 1) = (X - 26) * P(X) and show that
  -- P = c * ∏ i ∈ range 26, (X - i) for some c ∈ ℝ.
  intro h
  have he (x : ℝ) : x * P.eval (x - 1) = (x - 26) * P.eval x := by
    apply_fun eval x at h
    simp_all
  -- Consider two cases: P = 0 and P ≠ 0.
  by_cases hP0 : P = 0
  · -- If P = 0 then use c = 0.
    use 0
    simp [hP0]
  -- Assume now that P ≠ 0.
  -- Define s = {0, 1, ... , 25} (as Multiset ℝ).
  set s : Multiset ℝ := (Multiset.range 26).map (fun x : ℕ => (x : ℝ))
  -- Show that s ≤ P.roots.
  have hr : s ≤ P.roots := by
    -- We have x ∈ s ↔ ∃ i ∈ [0, 26), x = i.
    have hs (x : ℝ) : x ∈ s ↔ ∃ i ∈ range 26, x = i := by
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
    -- We have i < 26 and we need to show that P(i) = 0.
    simp
    -- Proof by induction.
    induction i with
    | zero =>
      -- P(0) * (0 - 26) = 0 * P(0 - 1), so P(0) = 0.
      simp [hP0]
      have := he 0
      simp at this
      exact this
    | succ i ih =>
      -- Consider P(i + 1), i + 1 < 26.
      simp [hP0]
      -- We have (i + 1 - 26) * P(i + 1) = (i + 1) * P(i + 1 - 1).
      -- We have i + 1 - 26 ≠ 0 and P(i + 1 - 1) = P(i) = 0, so
      -- P(i + 1) = 0.
      have := he (i + 1)
      simp [ih (by omega)] at this
      cases' this with h h
      · replace hi : i + 1 ≤ 25 := by omega
        rify at hi
        linarith
      exact h
  -- s ≤ P.roots implies that P = Q * ∏ i ∈ range 26, (X - i) for some polynomial Q.
  have ⟨Q, hPQ⟩ : ∃ Q : ℝ[X], P = Q * ∏ i ∈ range 26, (X - C (i : ℝ)) := by
    have ⟨Q, hQ⟩ := (Multiset.prod_X_sub_C_dvd_iff_le_roots hP0 s).mpr hr
    use Q
    rw [hQ, mul_comm]
    rfl
  -- Show that Q(x - 1) = Q(x) for all 26 < x.
  have hQ {x : ℝ} (hx : 26 < x) : Q.eval (x - 1) = Q.eval x := by
    -- We have x * P(x - 1) = (x - 26) * P(x) and
    -- P(x) = Q(x) * ∏ i ∈ range 26, (x - i).
    replace he := he x
    simp [hPQ, eval_prod] at he
    -- We proved that x * ∏ i ∈ range 26, (x - i - 1) = (x - 26) * ∏ i ∈ range 26, (x - i),
    -- so we get Q(x - 1) * ((x - 26) * ∏ i ∈ range 26, (x - i)) = Q(x) * ((x - 26) * ∏ i ∈ range 26, (x - i)).
    rw [mul_left_comm, eq, mul_left_comm (x - 26)] at he
    -- It is left to show that (x - 26) * ∏ i ∈ range 26, (x - i) ≠ 0.
    rwa [mul_left_inj'] at he
    -- We have 26 < x, so x - 26 > 0 and ∏ i ∈ range 26, (x - i) > 0.
    apply ne_of_gt
    apply mul_pos (by linarith)
    apply prod_pos
    simp only [mem_range, sub_pos]
    intro i hi
    rify at hi
    linarith
  -- Show that Q = C c for some c ∈ ℝ.
  have ⟨c, hc⟩ : ∃ c, Q = C c := by
    -- Show that Q = C (Q(30)).
    use eval 30 Q
    -- It is enough to show that Q(30 + i) = Q(30) for all i ∈ [0, Q.natDegree + 1)
    -- and [0, Q.natDegree + 1).card > Q.natDegree.
    apply eq_const_of_natDegree_lt_card_of_eval_eq ((Finset.range (1 + Q.natDegree)).image (fun n : ℕ => 30 + (n : ℝ)))
    · simp only [mem_image, mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro i hi
      -- Proof by induction.
      induction i with
      -- Q(30 + 0) = Q(30).
      | zero => simp
      | succ i ih =>
        -- Q(30 + i + 1) = Q (30 + i + 1 - 1) = Q(30 + i) = Q(30) (since 30 + i > 26).
        rw [← ih (by omega), ← hQ (by linarith)]
        congr
        push_cast
        ring
    · -- [0, Q.natDegree + 1).card = Q.natDegree + 1 > Q.natDegree.
      rw [card_image_of_injective _ (by intro x y; simp)]
      simp only [card_range, lt_add_iff_pos_left, zero_lt_one]
  -- Q = C c, so P = C c * ∏ i ∈ range 26, (X - i).
  use c
  rw [hPQ, hc]