import Mathlib
open Real Finset 
set_option maxHeartbeats 350000
noncomputable section

-- Define $2D$ lattice points.
abbrev Point := ℤ × ℤ

-- Calculate triangle area (using determinant, absolute value divided by $2$).
def triangle_area (p1 p2 p3 : Point) : ℝ :=
  let v1 := (p2.1 - p1.1, p2.2 - p1.2)
  let v2 := (p3.1 - p1.1, p3.2 - p1.2)
  abs (v1.1 * v2.2 - v1.2 * v2.1) / 2

-- Lemma: If $AB$ and $CD$ are parallel, then triangles $ABC$ and $ABD$ have equal areas.
lemma area_equal_if_parallel (A B C D : Point) :
  let v_AB := (B.1 - A.1, B.2 - A.2)
  let v_CD := (D.1 - C.1, D.2 - C.2)
  v_AB.1 * v_CD.2 = v_AB.2 * v_CD.1 → 
  triangle_area A B C = triangle_area A B D := by
  intros v_AB v_CD h_parallel
  -- Calculate the area of triangle $ABC$.
  have h_ABC : triangle_area A B C =
      abs ((B.1 - A.1) * (C.2 - A.2) - (B.2 - A.2) * (C.1 - A.1)) / 2 := by
    simp [triangle_area, sub_mul, mul_sub]
  -- Calculate the area of triangle $ABD$.
  have h_ABD : triangle_area A B D =
      abs ((B.1 - A.1) * (D.2 - A.2) - (B.2 - A.2) * (D.1 - A.1)) / 2 := by
    simp [triangle_area, sub_mul, mul_sub]
  -- Use the parallel condition to substitute D's coordinates.
  have h_parallel_eq : (B.1 - A.1) * (D.2 - C.2) = (B.2 - A.2) * (D.1 - C.1) := by
    simp [v_AB, v_CD] at h_parallel
    exact h_parallel
  -- Prove the areas are equal.
  have h_area_eq : triangle_area A B C = triangle_area A B D := by
    rw [h_ABC, h_ABD]
    set x := B.1 - A.1
    set y := B.2 - A.2
    set z := C.1 - A.1
    set w := C.2 - A.2
    set u := D.1 - A.1
    set v := D.2 - A.2
    have h_D : x * (v - w) = y * (u - z) := by
      simp [x, y, z, w, u, v, h_parallel_eq]
    suffices abs (x * w - y * z) = abs (x * v - y * u) by
      field_simp [this]
    have h_v : x * v - y * u = x * w - y * z := by
      rw [sub_eq_sub_iff_sub_eq_sub]
      ring_nf
      unfold x v w y u z at h_D
      ring_nf at h_D
      exact h_D
    rw [h_v]
  exact h_area_eq

/-Trois sauterelles se trouvent aux points $(0,0),(0,1)$ et $(1,0)$ d'une feuille quadrillée. Chaque minute une sauterelle saute sur un autre point de la grille d'une telle façon que son saut soit parallèle à la droite passant par les deux autres sauterelles. Est-il possible qu'au bout d'un certain temps les sauterelles se retrouvent aux points $(-1,0),(1,0)$ et $(0,1)$ ?-/
theorem logic_and_puzzles_2012345 : ¬∃ t : ℕ, ∃ positions : ℕ → (Point × Point × Point),
  positions 0 = ((0, 0), (0, 1), (1, 0)) ∧
  (∀ n, ∃ i : Fin 3, ∃ new_pos : Point,
    let old_pos := positions n
    let other1 := if i = 0 then old_pos.2.1 else if i = 1 then old_pos.1 else old_pos.1
    let other2 := if i = 0 then old_pos.2.2 else if i = 1 then old_pos.2.2 else old_pos.2.1
    let v_jump := (new_pos.1 - (if i = 0 then old_pos.1.1 else if i = 1 then old_pos.2.1.1 else old_pos.2.2.1),
                   new_pos.2 - (if i = 0 then old_pos.1.2 else if i = 1 then old_pos.2.1.2 else old_pos.2.2.2))
    let v_other := (other2.1 - other1.1, other2.2 - other1.2)
    v_jump.1 * v_other.2 = v_jump.2 * v_other.1 ∧ 
    positions (n + 1) = if i = 0 then (new_pos, old_pos.2.1, old_pos.2.2)
                       else if i = 1 then (old_pos.1, new_pos, old_pos.2.2)
                       else (old_pos.1, old_pos.2.1, new_pos)) ∧
  positions t = ((-1, 0), (1, 0), (0, 1)) := by
  -- Prove the target is impossible: initial and target triangle areas differ.
  intro h_exists
  obtain ⟨t, positions, h_init, h_moves, h_final⟩ := h_exists
  -- Subgoal $1$: Each jump preserves the triangle area.
  have h_area_invariant : ∀ n, triangle_area (positions n).1 (positions n).2.1 (positions n).2.2 =
      triangle_area (positions 0).1 (positions 0).2.1 (positions 0).2.2 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      obtain ⟨i, new_pos, h_parallel, h_next⟩ := h_moves n
      set old_pos := positions n
      set new_pos_triple := positions (n + 1)
      fin_cases i <;> simp [h_next]
      · -- First grasshopper jumps.
        have h_par : (old_pos.2.2.1 - old_pos.2.1.1) * (new_pos.2 - old_pos.1.2) =
                     (old_pos.2.2.2 - old_pos.2.1.2) * (new_pos.1 - old_pos.1.1) := by
          simp_all [Fin.forall_fin_succ, Fin.forall_fin_succ']
          ring_nf at *
          norm_num at *
          aesop
        have h_area_eq : triangle_area new_pos old_pos.2.1 old_pos.2.2 = triangle_area (positions 0).1 (positions 0).2.1 (positions 0).2.2 := by
          have h_eq : triangle_area old_pos.1 old_pos.2.1 old_pos.2.2 = triangle_area new_pos old_pos.2.1 old_pos.2.2 := by
            have h_old_order : triangle_area old_pos.1 old_pos.2.1 old_pos.2.2 = triangle_area old_pos.2.1 old_pos.2.2 old_pos.1 := by
              simp [triangle_area]
              ring_nf
            have h_new_order : triangle_area old_pos.2.1 old_pos.2.2 new_pos = triangle_area new_pos old_pos.2.1 old_pos.2.2 := by
              simp [triangle_area]
              ring_nf
            rw [h_old_order, ← h_new_order]
            apply area_equal_if_parallel old_pos.2.1 old_pos.2.2 old_pos.1 new_pos
            exact h_par
          rw [← h_eq]
          exact ih
        exact h_area_eq
      · -- Second grasshopper jumps.
        have h_par : (old_pos.2.2.1 - old_pos.1.1) * (new_pos.2 - old_pos.2.1.2) =
                   (old_pos.2.2.2 - old_pos.1.2) * (new_pos.1 - old_pos.2.1.1) := by
          simp_all [Fin.forall_fin_succ, Fin.forall_fin_succ']
          ring_nf at *
          norm_num at *
          aesop
        have h_area_eq : triangle_area old_pos.1 new_pos old_pos.2.2 = triangle_area (positions 0).1 (positions 0).2.1 (positions 0).2.2 := by
          have h_eq : triangle_area old_pos.1 old_pos.2.1 old_pos.2.2 = triangle_area old_pos.1 new_pos old_pos.2.2 := by
            have h_old_order : triangle_area old_pos.1 old_pos.2.1 old_pos.2.2 = triangle_area old_pos.1 old_pos.2.2 old_pos.2.1 := by
              simp only [triangle_area]
              set x1 := old_pos.1.1
              set y1 := old_pos.1.2
              set x2 := old_pos.2.1.1
              set y2 := old_pos.2.1.2
              set x3 := old_pos.2.2.1
              set y3 := old_pos.2.2.2
              have h_left : (x2 - x1) * (y3 - y1) - (y2 - y1) * (x3 - x1) = -((x3 - x1) * (y2 - y1) - (y3 - y1) * (x2 - x1)) := by
                ring
              rw [h_left]
              simp only [abs_neg]
            have h_new_order : triangle_area old_pos.1 old_pos.2.2 new_pos = triangle_area old_pos.1 new_pos old_pos.2.2 := by
              simp only [triangle_area]
              set x1 := old_pos.1.1
              set y1 := old_pos.1.2
              set x3 := old_pos.2.2.1
              set y3 := old_pos.2.2.2
              set x4 := new_pos.1
              set y4 := new_pos.2
              have h_left : (x3 - x1) * (y4 - y1) - (y3 - y1) * (x4 - x1) = -((x4 - x1) * (y3 - y1) - (y4 - y1) * (x3 - x1)) := by
                ring
              rw [h_left]
              simp only [abs_neg]
            rw [h_old_order, ← h_new_order]
            apply area_equal_if_parallel old_pos.1 old_pos.2.2 old_pos.2.1 new_pos
            exact h_par
          rw [← h_eq]
          exact ih
        exact h_area_eq
      · -- Third grasshopper jumps.
        have h_par : (old_pos.2.1.1 - old_pos.1.1) * (new_pos.2 - old_pos.2.2.2) =
                   (old_pos.2.1.2 - old_pos.1.2) * (new_pos.1 - old_pos.2.2.1) := by
          simp_all [Fin.forall_fin_succ, Fin.forall_fin_succ']
          ring_nf at *
          norm_num at *
          aesop
        have h_area_eq : triangle_area old_pos.1 old_pos.2.1 new_pos = triangle_area (positions 0).1 (positions 0).2.1 (positions 0).2.2 := by
          have h_eq : triangle_area old_pos.1 old_pos.2.1 old_pos.2.2 = triangle_area old_pos.1 old_pos.2.1 new_pos := by
            apply area_equal_if_parallel old_pos.1 old_pos.2.1 old_pos.2.2 new_pos
            exact h_par
          rw [← h_eq]
          exact ih
        exact h_area_eq
  -- Subgoal $2$: Initial triangle area is $1/2$.
  have h_init_area : triangle_area (positions 0).1 (positions 0).2.1 (positions 0).2.2 = 1 / 2 := by
    simp [h_init, triangle_area]
  -- Subgoal $3$: Target triangle area is $1$.
  have h_final_area : triangle_area (positions t).1 (positions t).2.1 (positions t).2.2 = 1 := by
    simp [h_final, triangle_area]
  -- Subgoal $4$: Area invariance leads to contradiction.
  have h_contradiction : False := by
    have h_area_eq : triangle_area (positions t).1 (positions t).2.1 (positions t).2.2 =
                     triangle_area (positions 0).1 (positions 0).2.1 (positions 0).2.2 := by
      apply h_area_invariant
    rw [h_final_area, h_init_area] at h_area_eq
    norm_num at h_area_eq
  exact h_contradiction
