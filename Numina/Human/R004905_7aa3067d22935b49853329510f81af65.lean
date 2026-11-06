import Mathlib

namespace number_theory_604546

def int_coordinates (p: EuclideanSpace ℝ (Fin 2)) :=
  (∃ m:ℤ, m = p 0) ∧ (∃ m:ℤ, m = p 1)

end number_theory_604546

open number_theory_604546

/- Let $P_{1}, P_{2}, \ldots, P_{1993}=P_{0}$ be distinct points in the $x y$-plane with the following properties:
(i) both coordinates of $P_{i}$ are integers, for $i=1,2, \ldots, 1993$;
(ii) there is no point other than $P_{i}$ and $P_{i+1}$ on the line segment joining $P_{i}$ with $P_{i+1}$ whose coordinates are both integers, for $i=0,1, \ldots, 1992$.

Prove that for some $i, 0 \leq i \leq 1992$, there exists a point $Q$ with coordinates $\left(q_{x}, q_{y}\right)$ on the line segment joining $P_{i}$ with $P_{i+1}$ such that both $2 q_{x}$ and $2 q_{y}$ are odd integers. -/
theorem number_theory_604546 {P : Fin 1993 → (EuclideanSpace ℝ (Fin 2))}
  (h0: ∀ i j, P i = P j → i = j)
  (h1: ∀i, int_coordinates (P i) )
  (h2: ∀i, ∀q,
    Sbtw ℝ (P i) q (P (i+1)) → ¬ int_coordinates q):
  ∃ i, ∃ q,
  Sbtw ℝ (P i) q (P (i+1)) ∧
  (∃ m:ℤ, Odd m ∧ m = 2 * q 0) ∧
  (∃ m:ℤ, Odd m ∧ m = 2 * q 1) := by

  -- if we can find two points p1, p2 such that x1+x2 is odd and y1+y2 is odd,
  -- then their mid point is the answer.
  suffices h: ∃ i,
    (∃ m:ℤ, Odd m ∧ m = (P i) 0 + (P (i+1)) 0) ∧
    (∃ m:ℤ, Odd m ∧ m = (P i) 1 + (P (i+1)) 1) by
    rcases h with ⟨i, hi1, hi2⟩
    set q := midpoint ℝ (P i) (P (i+1)) with q_def
    use i,q
    refine ⟨?_, ?_, ?_⟩
    · rw [q_def]
      refine sbtw_midpoint_of_ne ℝ ?_
      rintro heq
      specialize h0 i (i+1) heq
      simp at h0
    · rw [show 2 * q 0 = (2 • q) 0 by simp,
      two_smul, q_def, midpoint_add_self]
      simpa only [Fin.isValue, PiLp.add_apply] using hi1
    · rw [show 2 * q 1 = (2 • q) 1 by simp,
      two_smul, q_def, midpoint_add_self]
      simpa only [Fin.isValue, PiLp.add_apply] using hi2

  -- consider a function compute x1+y1 for point (x1,y1).
  delta int_coordinates at h1
  have: ∀i, ∃ m:ℤ, m = (P i) 0 + (P i) 1 := by
    intro i
    specialize h1 i
    rcases h1 with ⟨ ⟨m1, hm1⟩, ⟨m2, hm2⟩ ⟩
    use m1+m2
    rw [← hm1, ← hm2]
    simp
  choose f hf using this

  -- we claim if n is an odd number, g is function from Fin n to ℤ,
  -- then must exist i, such that g i and g_{i+1} have same parity.
  have (n:ℕ) (g: Fin n → ℤ) (hn: 1 < n) (hhn: Odd n): ∃ i: Fin n,
    (Odd (g i) ∧ Odd (g (i+ ⟨1,hn⟩)) ) ∨
    (Even (g i) ∧ Even (g (i + ⟨1,hn⟩)) ) := by
    have npos: 0 < n := Nat.zero_lt_of_lt hn
    by_contra! hh
    rw [odd_iff_exists_bit1] at hhn
    rcases hhn with ⟨m, hm⟩
    by_cases hh1: Odd (g ⟨0,npos⟩)
    · -- g0 odd case. if g0 is odd, then must be the case g0, g2, g4,... odd,
      -- and g1, g3, g5, ... even.
      have hh2 (m': ℕ) (hm': m' < m):
        Odd (g ⟨2*m', (by omega)⟩) ∧ Even (g ⟨2*m'+1, (by omega)⟩) := by
        induction' m' with m' ih
        · simp only [mul_zero, hh1, zero_add, true_and]
          have := (hh ⟨0, npos⟩).left hh1
          rw [Int.not_odd_iff_even] at this
          convert this
          rw [Fin.val_add_eq_ite, if_neg (by simp [hn])]
          simp
        · have hh2: Odd (g ⟨2*(m'+1), (by omega)⟩ ) := by
            have hhm: 2*m'+1 < n := by
              rw [hm]
              linarith only [hm']
            have hhm': m' < m := lt_trans (by simp) hm'
            have := (hh ⟨2*m'+1, hhm⟩).right (ih hhm').right
            rw [Int.not_even_iff_odd] at this
            convert this
            rw [Fin.val_add_eq_ite, if_neg]
            simp [Nat.mul_add_one]
            push_neg
            simp only [hm, add_lt_add_iff_right]
            omega
          refine ⟨hh2, ?_⟩
          have := (hh ⟨2*(m'+1), (by omega)⟩).left hh2
          rw [Int.not_odd_iff_even] at this
          convert this
          rw [Fin.val_add_eq_ite, if_neg]
          simp [hm, hm']
      have hh3: Odd (g ⟨2*m, by simp [hm]⟩) := by
        have mpos: 0 < m := by
          omega
        specialize hh2 (m-1) (by simp [mpos])
        have := (hh ⟨(2*(m-1)+1), by omega⟩).right hh2.right
        rw [Int.not_even_iff_odd] at this
        convert this
        rw [Fin.val_add_eq_ite, if_neg]
        simp only
        omega
        simp only [hm, add_le_add_iff_right, not_le]
        omega
      -- but the index Fin (2m+1) is periodic. say, g_{2m+1} is just g0.
      -- so we can prove g_{2m+1} is even, but we know it is g0 and g0 is odd.
      -- thus we reach a contradiction.
      replace hh3 := (hh ⟨2*m, by simp [hm]⟩).left hh3
      absurd hh1
      convert hh3
      rw [Fin.val_add_eq_ite, if_pos]
      <;> simp [hm]
    · -- g0 even case.
      -- if g0 is even, then must be the case g0, g2, g4, ... even,
      -- with g1, g3, g5, ... odd.
      rw [Int.not_odd_iff_even] at hh1
      have hh2 (m': ℕ) (hm': m' < m):
        Even (g ⟨2*m', (by omega)⟩) ∧ Odd (g ⟨2*m'+1, (by omega)⟩) := by
        induction' m' with m' ih
        · simp only [mul_zero, hh1, zero_add, true_and]
          have := (hh ⟨0, npos⟩).right hh1
          rw [Int.not_even_iff_odd] at this
          convert this
          rw [Fin.val_add_eq_ite, if_neg (by simp [hn])]
          simp
        · have hh2: Even (g ⟨2*(m'+1), (by omega)⟩ ) := by
            have hhm: 2*m'+1 < n := by
              rw [hm]
              linarith only [hm']
            have hhm': m' < m := lt_trans (by simp) hm'
            have := (hh ⟨2*m'+1, hhm⟩).left (ih hhm').right
            rw [Int.not_odd_iff_even] at this
            convert this
            rw [Fin.val_add_eq_ite, if_neg]
            simp [Nat.mul_add_one]
            push_neg
            simp only [hm, add_lt_add_iff_right]
            omega
          refine ⟨hh2, ?_⟩
          have := (hh ⟨2*(m'+1), (by omega)⟩).right hh2
          rw [Int.not_even_iff_odd] at this
          convert this
          rw [Fin.val_add_eq_ite, if_neg]
          simp [hm, hm']
      have hh3: Even (g ⟨2*m, by simp [hm]⟩) := by
        have mpos: 0 < m := by
          omega
        specialize hh2 (m-1) (by simp [mpos])
        have := (hh ⟨(2*(m-1)+1), by omega⟩).left hh2.right
        rw [Int.not_odd_iff_even] at this
        convert this
        rw [Fin.val_add_eq_ite, if_neg]
        simp only
        omega
        simp only [hm, add_le_add_iff_right, not_le]
        omega
      -- from discussion above, we know g_{2m+1} is odd.
      -- but the index Fin n is periodic, and g_{2m+1} is just g0m it's even.
      -- thus contradiction.
      replace hh3 := (hh ⟨2*m, by simp [hm]⟩).right hh3
      absurd hh1
      convert hh3
      rw [Fin.val_add_eq_ite, if_pos]
      <;> simp [hm]

  -- then we can choose such i
  specialize this 1993 f (by norm_num) (by exact Nat.odd_iff.mpr rfl)
  rcases this with ⟨i, h⟩
  simp only [Fin.mk_one, Fin.isValue] at h
  -- let x,y compute their x-, y- coordinates.
  choose x hx using (fun j => (h1 j).left)
  choose y hy using (fun j => (h1 j).right)
  -- we claim x_i + y_i + x_{i+1} + y_{i+1} = (x_i + x_{i+1}) + (y_i + y_{i+1}) is even.
  replace h: Even (x i + x (i+1) + (y i + y (i+1)) ) := by
    have: x i + x (i+1) + (y i + y (i+1)) =
      (x i + y i) + (x (i+1) + y (i+1)) := by ring
    have hh1: f i = x i + y i := by
      rify
      rw [hx, hy, hf]
    have hh2: f (i+1) = x (i+1) + y (i+1) := by
      rify
      rw [hx, hy, hf]
    rw [this, ← hh1, ← hh2]
    rcases h with h | h
    · exact Odd.add_odd h.left h.right
    · exact Even.add h.left h.right
  use i

  -- if x_i + x_{i+1}, y_i + y_{i+1} are both odd, done.
  by_cases hh: Odd (x i + x (i+1))
  · constructor
    · use (x i + x (i+1)),hh
      simp [hx]
    · rw [Int.even_add'] at h
      use (y i + y (i+1)), (h.mp hh)
      simp [hy]
  · -- otherwise, both are even.
    rw [Int.not_odd_iff_even] at hh
    rw [Int.even_add] at h
    -- and we claim their mid point has integer coordinates.
    -- therefore contradiction to problem statement.
    set q := midpoint ℝ (P i) (P (i+1)) with q_def
    have hq: Sbtw ℝ (P i) q (P (i+1)) := by
      rw [q_def]
      refine sbtw_midpoint_of_ne ℝ ?_
      rintro heq
      specialize h0 i (i+1) heq
      simp at h0
    specialize h2 i q hq
    absurd h2
    delta int_coordinates
    rw [q_def, midpoint_eq_smul_add]
    simp only [Fin.isValue, invOf_eq_inv, PiLp.smul_apply,
    PiLp.add_apply, smul_eq_mul]
    replace h := h.mp hh
    rw [even_iff_exists_two_mul] at h hh
    have xadd: P i 0 + P (i+1) 0 = ↑(x i + x (i+1): ℤ) := by
      simp [hx]
    have yadd: P i 1 + P (i+1) 1 = ↑(y i + y (i+1): ℤ) := by
      simp [hy]
    rcases hh with ⟨a, ha⟩
    rcases h with ⟨b, hb⟩
    rw [xadd, yadd, ha, hb]
    simp