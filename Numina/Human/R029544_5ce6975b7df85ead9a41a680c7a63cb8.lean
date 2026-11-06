import Mathlib

def equation (y : ℝ) (x : Fin 5 → ℝ) : Prop :=
  ∀ i, x i + x (i + 2) = y * x (i + 1)

theorem Other_4663 (y : ℝ) (x : Fin 5 → ℝ) :
    if y = 2 then
      equation y x ↔ ∀ i j, x i = x j
    else if y^2 + y - 1 ≠ 0 then
      equation y x ↔ ∀ i, x i = 0
    else
      equation y x ↔ x 1 = y * x 0 - x 4 ∧ x 2 = (y^2 - 1) * x 0 - y * x 4 ∧ x 3 = y * x 4 - x 0 := by
  -- Summing up all the equations yields $2\left(x_{1}+x_{2}+x_{3}+x_{4}+x_{5}\right)=y\left(x_{1}+\right.$ $x_{2}+x_{3}+x_{4}+x_{5}$ ).
  have h1 (h : equation y x) : 2 * (x 0 + x 1 + x 2 + x 3 + x 4) = y * (x 0 + x 1 + x 2 + x 3 + x 4) := by
    calc
      _ = (x 0 + x (0 + 2)) + (x 1 + x (1 + 2)) + (x 2 + x (2 + 2)) + (x 3 + x (3 + 2)) + (x 4 + x (4 + 2)) := by
        simp
        ring
      _ = _ := by
        rw [h 0, h 1, h 2, h 3, h 4]
        simp
        ring
  split
  case isTrue hy1 =>
    constructor
    · intro h
      simp [equation, hy1] at h
      -- If $y=2$, then the given equations imply $x_{1}-x_{2}=$ $x_{2}-x_{3}=\cdots=x_{5}-x_{1}$;
      have h2 : ∀ i, x i - x (i + 1) = 0 := by
        intro i
        have := h 0; simp at this
        have := h 1; simp at this
        have := h 2; simp at this
        have := h 3; simp at this
        have := h 4; simp at this
        fin_cases i <;> simp <;> linarith
      -- hence $x_{1}=x_{2}=\cdots=x_{5}$,
      intro i j
      have := h2 0; simp at this
      have := h2 1; simp at this
      have := h2 2; simp at this
      have := h2 3; simp at this
      have := h2 4; simp at this
      fin_cases i <;> fin_cases j <;> simp <;> linarith
    -- which is clearly a solution.
    · intro h i
      simp [hy1]
      rw [h i (i + 2), h (i + 1) (i + 2)]
      ring
  case isFalse hy1 =>
    -- If $y \neq 2$, then $x_{1}+\cdots+x_{5}=0$,
    replace h1 (h : equation y x) : x 0 + x 1 + x 2 + x 3 + x 4 = 0 := by
      replace hy1 : 2 ≠ y := by symm; assumption
      simp at hy1
      simp [hy1] at h1
      solve_by_elim
    -- and summing any three consecutive equalities gives $x_{i}=y\left(x_{i - 1}+x_{i}+x_{i + 1}\right)$.
    -- Using that $x_{i - 1}+x_{i + 1}=y x_{i}$ we obtain $x_{i}=\left(y^{2}+y\right) x_{i}$,
    have h3 (h : equation y x) : ∀ i, x i = (y^2 + y) * x i := by
      specialize h1 h
      have := h 0; simp at this
      have := h 1; simp at this
      have := h 2; simp at this
      have := h 3; simp at this
      have := h 4; simp at this
      intro i
      have : x i = y * (x (i - 1) + x i + x (i + 1)) := by
        fin_cases i <;> simp [show (-1 : Fin 5) = (4 : Fin 5) by rfl] <;> linarith
      rw [show i + 1 = (i - 1) + 2 by omega] at this
      rw [show x (i - 1) + x i + x ((i - 1) + 2)= x (i - 1) + x ((i - 1) + 2) + x i by ring] at this
      conv => lhs; rw [this, h (i - 1)]; simp
      ring
    -- i.e., $\left(y^{2}+y-1\right) x_{i}=0$.
    replace h3 (h : equation y x) : ∀ i, (y^2 + y - 1) * x i = 0 := by
      intro i
      have := h3 h i
      linarith
    split_ifs with hy2
    -- If $y^{2}+y-1 \neq 0$, then $x_{i}=0$ for all $i$.
    · simp [hy2] at h3
      refine ⟨h3, ?_⟩
      intro h i
      rw [h, h, h]
      simp
    -- If $y^{2}+y-1=0$, it is easy to prove that the last two equations are the consequence of the first three.
    -- Thus choosing any values for $x_{1}$ and $x_{5}$ will give exactly one solution for $x_{2}, x_{3}, x_{4}$.
    · simp at hy2
      replace hy2 : y^2 = 1 - y := by linarith
      constructor
      · intro h
        have := h 0; simp at this
        have := h 1; simp at this
        have := h 2; simp at this
        have := h 3; simp at this
        have := h 4; simp at this
        have h1_eq : x 1 = y * x 0 - x 4 := by linarith
        have h3_eq : x 3 = y * x 4 - x 0 := by linarith
        refine ⟨h1_eq, ?_, h3_eq⟩
        calc
          _ = y * x 1 - x 0 := by linarith
          _ = _ := by
            rw [h1_eq]
            ring
      · intro ⟨h1, h2, h3⟩
        intro i
        fin_cases i <;> simp [h1, h2, h3] <;> try ring_nf
        · rw [show y^3 = y^2 * y by ring, hy2]
          ring_nf
          rw [hy2]
          ring
        · rw [hy2]
          ring
