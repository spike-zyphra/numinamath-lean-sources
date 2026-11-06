import Mathlib

/- Let's prove that every non-negative integer can be uniquely expressed in the form
$$ \frac{(x+y)^{2}+3 x+y}{2} $$
where $x$ and $y$ are non-negative integers. -/

theorem number_theory_207426 (n : ℕ) :
    ∃! xy : ℕ × ℕ, n = ((xy.1 + xy.2)^2 + 3 * xy.1 + xy.2) / 2 := by

  -- We prove first by induction an euclidean division-style lemma: every non-negative integer can be expressed
  -- uniquely as the sum of a triangular number and a non-negative integer less than the index of the triangular number.
  have (n : ℕ) : ∃! mr : ℕ × ℕ, mr.2 < mr.1 ∧ mr.1.choose 2 + mr.2 = n := by
    induction' n with n ih
    -- If n = 0, the only solution is (1, 0).
    · use (1, 0)
      simp only [zero_lt_one, Nat.choose_succ_self, add_zero, and_self, and_imp, Prod.forall,
        Prod.mk.injEq, true_and]
      intro a b hab h
      rw [Nat.add_eq_zero_iff] at h
      constructor
      · have := Nat.choose_eq_zero_iff.mp h.1
        linarith
      · exact h.2
    -- If we know the result for n, we can prove it for n+1. Let m, r, be the solution for n.
    · obtain ⟨⟨m, r⟩, ⟨hmr, hn⟩, h⟩ := ih
      simp only [and_imp, Prod.forall, Prod.mk.injEq] at *
      by_cases hr : r+1 < m
      -- If r+1 < m, we can use the same solution (m, r+1).
      · use (m, r+1)
        constructor
        -- The validity is obvious.
        · constructor
          · exact hr
          · rw [← hn]; ring
        -- The uniqueness is less trivial. Let's suppose we have another solution (a, b) for n+1.
        · intro ⟨a, b⟩ ⟨hab, hn'⟩
          simp only [Prod.mk.injEq] at *
          by_cases hb0 : 0 < b
          -- If b > 0, we can use the uniqueness of the solution for n by subtracting 1.
          · obtain ⟨ha, hb⟩ := h a (b-1) (tsub_lt_of_lt hab) (by omega)
            constructor
            · exact ha
            · omega
          -- If b = 0, we find another solution for n, which leads to a contradiction.
          · have ha0 : a > 1 := by
              by_contra h
              simp only [not_lt, nonpos_iff_eq_zero, gt_iff_lt] at *
              have h : a = 1 := by linarith
              rw [h, hb0] at hn'
              contradiction
            obtain ⟨ha, hb⟩ := h (a-1) (a-2) (by omega) (by
              simp only [not_lt, nonpos_iff_eq_zero] at hb0
              rw [hb0, (by omega : a = a - 1 + 1), Nat.choose_succ_left] at hn'
              simp only [Nat.add_one_sub_one, Nat.choose_one_right, add_zero] at hn'
              omega; linarith)
            rw [← ha, ← hb] at hr
            omega
      -- If r+1 = m, we can use the solution (m+1, 0).
      · use (m+1, 0)
        constructor
        -- Again, the validity is obvious.
        · constructor
          · linarith
          · dsimp
            rw [← hn, add_assoc, (by linarith : r+1 = m), Nat.choose_succ_left,
              Nat.add_one_sub_one, Nat.choose_one_right, add_comm]
            linarith
        -- The uniqueness is again less trivial. Let's suppose we have another solution (a, b) for n+1.
        · intro ⟨a, b⟩ ⟨hab, hn'⟩
          simp only [Prod.mk.injEq] at *
          have hr : m = r + 1 := by linarith
          by_cases hb0 : 0 < b
          -- If b > 0, we can find a contradiction by subtracting 1.
          · obtain ⟨ha, hb⟩ := h a (b-1) (tsub_lt_of_lt hab) (by omega)
            rw [hr, ← hb, Nat.sub_add_cancel (by exact hb0)] at ha
            rw [ha] at hab
            exfalso
            exact (lt_self_iff_false b).mp hab
          -- If b = 0, we use the uniqueness of the solution for n by subtracting 1 and reconstructing the solution.
          · have ha0 : a > 1 := by
              by_contra h
              simp only [not_lt, nonpos_iff_eq_zero, gt_iff_lt] at *
              have h : a = 1 := by linarith
              rw [h, hb0] at hn'
              contradiction
            obtain ⟨ha, hb⟩ := h (a-1) (a-2) (by omega) (by
              simp only [not_lt, nonpos_iff_eq_zero] at hb0
              rw [hb0, (by omega : a = a - 1 + 1), Nat.choose_succ_left] at hn'
              simp only [Nat.add_one_sub_one, Nat.choose_one_right, add_zero] at hn'
              omega; linarith)
            constructor
            · omega
            · exact Nat.eq_zero_of_not_pos hb0

  -- Via an algebraic manipulation, we can rewrite our formula as a sum of a triangular number and a non-negative integer less than the index of the triangular number.
  have binom (x y : ℕ) : ((x + y)^2 + 3 * x + y) / 2 = (x + y + 1).choose 2 + x := by
    have : (x + y + 1) * (x + y) / 2 + x = ((x + y + 1) * (x + y) + 2 * x) / 2 := by omega
    rw [Nat.choose_two_right, add_tsub_cancel_right, this]; ring_nf

  -- Now we use the previous result to complete the proof.
  obtain ⟨⟨m, r⟩, ⟨hmr, hn⟩, h⟩ := this n
  use (r, m-r-1)
  simp only [and_imp, Prod.forall, Prod.mk.injEq] at *
  constructor
  · rw [binom r (m - r - 1), (by omega : r + (m - r - 1) + 1 = m)]
    exact hn.symm
  · simp_rw [binom]
    intro a b hn'
    have ⟨hb, ha⟩ := h (a+b+1) a (by linarith) hn'.symm
    constructor
    · exact ha
    · omega