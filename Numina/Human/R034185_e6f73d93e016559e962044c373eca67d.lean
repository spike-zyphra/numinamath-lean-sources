import Mathlib

/- For what ordered pair $(a,b)$ are there infinite solutions $(x,y)$ to the system \begin{align*}
2ax+2y&=b,\\
5x+y&=-3?
\end{align*} -/
theorem algebra_19720{s: Set (ℝ × ℝ)} (a b : ℝ)
  (hs: s = {(x,y):ℝ × ℝ | 2*a*x+2*y=b ∧ 5*x+y=-3}):
  Set.Infinite s ↔ a = 5 ∧ b = -6 := by
  -- for 2ax+2y=b, 5x+y=-3 have infinite solutions, first equation must be multiple of second equation. if not, we can solve x and y.
  -- if a ≠ 5, equations have unique solution.
  have h1(x y:ℝ)(ha: a ≠ 5): 2*a*x+2*y=b ∧ 5*x+y=-3 → x = (b+6)/(2*a-10) ∧ y = (-6*a-5*b)/(2*a-10) := by
    intro ⟨eq1,eq2⟩
    have eqy: y = -3-5*x := by
      rw [← eq2]; ring
    have eqx: (2*a-10)*x = b+6 := by
      rw [← eq1, eqy]; ring
    have: 2*a-10 ≠ 0 := by
      by_contra! hh1
      have hh2: a = 5 := by linarith [hh1]
      rw [hh2] at ha
      simp at ha
    have xeq: x = (b+6)/(2*a-10) := by
      rw [← eqx]; field_simp [this]
    have yeq: y = (-6*a-5*b)/(2*a-10) := by
      rw [xeq] at eqy; rw [eqy]
      field_simp [this]; ring
    exact ⟨xeq,yeq⟩
  -- and if a=5, we can solve b=-6.
  have h2'(x y:ℝ)(ha: a = 5): 2*a*x+2*y=b ∧ 5*x+y=-3 → b = -6 := by
    intro ⟨eq1,eq2⟩
    have: 2*a*x+2*y = 2*(5*x+y) := by
      rw [ha]; ring
    rw [this, eq2] at eq1
    rw [← eq1]; ring
  have h2(sinf: Set.Infinite s): a = 5 → b = -6 := by
    intro aeq
    by_contra! bne
    have: s = ∅ := by
      rw [hs]
      ext ⟨x,y⟩; simp
      intro hh1
      by_contra! hh2
      have := h2' x y aeq ⟨hh1,hh2⟩
      rw [this] at bne; simp at bne
    rw [this] at sinf; simp at sinf
  -- thus if it's not the cases that a=5 and b = -6, there is only one solution.
  have h3(ha: a ≠ 5): {(x,y):ℝ × ℝ | 2*a*x+2*y=b ∧ 5*x+y=-3} =
    {((b+6)/(2*a-10),(-6*a-5*b)/(2*a-10))} := by
    ext ⟨x,y⟩; simp
    constructor <;> intro h
    · have := h1 x y ha h
      rw [this.left, this.right]; simp
    · have: 2*a-10 ≠ 0 := by
        by_contra! hh1
        have hh2: a = 5 := by linarith [hh1]
        contradiction
      rw [h.left, h.right]
      field_simp [this]; ring_nf; simp
  -- a=5 and b = -6 is the only possible solution, otherwise solution set is not infinite.
  constructor
  · intro sinf
    by_cases ha: a=5
    · tauto
    · push_neg at ha
      rw [h3 ha] at hs
      rw [hs] at sinf; simp at sinf
  · intro ⟨aeq,beq⟩
    have h4: s = {(x,y) | y=-3-5*x} := by
      rw [hs,aeq,beq]
      ext ⟨x,y⟩
      simp
      constructor <;> intro h
      · linarith [h]
      · rw [h]; simp; ring
    apply Set.infinite_of_not_bddBelow
    rw [h4, BddBelow, lowerBounds]
    apply Set.not_nonempty_iff_eq_empty.mpr
    simp; ext ⟨x,y⟩
    simp
    by_cases hy: y < 0
    · use (-y)
      intro _
      linarith [hy]
    · push_neg at hy
      use y
      intro _
      linarith [hy]