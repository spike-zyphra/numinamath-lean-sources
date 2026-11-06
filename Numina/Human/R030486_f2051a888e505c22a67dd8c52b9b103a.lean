import Mathlib

/- 9 Let the coordinates of moving points $P$ and $P^{\prime}$ be $(x, y)$ and $\left(x^{\prime}, y^{\prime}\right)$, respectively, and they satisfy
$$
\left\{\begin{array}{l}
x^{\prime}=3 x+2 y+1, \\
y^{\prime}=x+4 y-3 .
\end{array}\right.
$$

If $P$ and $P^{\prime}$ move on the same straight line, does such a line exist? If it exists, find its equation. -/

theorem algebra_114503 {A B C: ℝ} (u: A ≠ 0 ∨ B ≠ 0):
   (∀ x' y' x y: ℝ, x' = 3 * x + 2 * y + 1 ∧ y' = x + 4 * y - 3 →
    (A * x' + B * y' + C = 0 ↔ A * x + B * y + C = 0)) ↔
    (A ≠ 0 ∧ B = - A ∧ C = 4 * A) ∨ (A ≠ 0 ∧ B = 2 * A ∧ C = -5 * A / 4) := by

  constructor
  -- the forward direction

  .
    intro h
    -- we simplify h by eliminating the variables x' and y'
    replace h: ∀ x y, A * x + B * y + C = 0 → (3 * A + B) * x + (2 * A + 4 * B) * y + (C + A - 3 * B) = 0 := by
      intro x y f
      specialize h (3 * x + 2 * y + 1) (x + 4 * y - 3) x y
      simp at h
      rw [← h] at f
      clear h
      nlinarith
     -- we show A ≠ 0
    have l: A ≠ 0 := by
      by_contra! l
      simp [l] at h
      have l2: B = 0 := by  -- then we must have B = 0
        by_contra! o  -- hence we can take y = - C / B, then choose x arbitrarily
        have h2:= h
        specialize h 0 (- C / B)
        have s: B * (-C / B) + C = 0 := by
          field_simp
          ring
        simp [s] at h
        field_simp at h
        ring_nf at h
        rw [show -(B * C * 3) - B ^ 2 * 3 = - 3 * B * (C + B) by ring] at h
        simp at h
        simp [o] at h
        specialize h2 1 (- C / B)
        simp [s] at h2
        field_simp at h2
        ring_nf at h2
        rw [show -(B * C * 3) - B ^ 2 * 2 = - B * (3 * C + 2 * B) by ring] at h2
        simp at h2
        simp [o] at h2
        have p: B = 0 := by nlinarith
        tauto
      simp [l2] at h
      absurd u
      simp [l,l2]
    -- then for all y, we can take x = -B * y + C / A to simplify the h
    simp [l]
    replace h: ∀ y, (2 * A ^ 2 - B ^ 2 + A * B) * y + ((C + A - 3 * B) * A - C * (3 * A + B)) = 0 := by
      intro y
      specialize h ((-B * y - C) / A) y
      field_simp at h
      ring_nf at h
      simp at h
      nlinarith
    have f1:= h 0  -- let y = 0
    simp at f1
    simp [f1] at h
    have f2:= h 1  -- let y = 1
    simp at f2
    clear h
    set t:= B / A with ht
    have lt: t ^ 2 - t - 2 = 0 := by
      simp [t]
      field_simp
      rw [show B ^ 2 * A - A ^ 2 * B - A ^ 2 * A * 2 = -A * (2 * A ^ 2 - B ^ 2 + A * B) by ring]
      simp [f2]
    rw [show t ^ 2 - t - 2 = (t - 2) * (t + 1) by ring] at lt
    simp at lt
    clear f2
    rcases lt with lt | lt
    .
      right
      simp [ht] at lt
      field_simp at lt
      replace lt: B = 2 * A := by
        linarith
      refine ⟨lt, ?_⟩
      simp [lt] at f1
      ring_nf at f1
      rw [show -(C * A * 4) - A ^ 2 * 5 = - A * (4 * C + 5 * A) by ring] at f1
      simp [l] at f1
      field_simp
      nlinarith
    .
      left
      simp [ht] at lt
      field_simp at lt
      replace lt: B = - A := by
        linarith
      refine ⟨lt, ?_⟩
      simp [lt] at f1
      ring_nf at f1
      rw [show -(C * A) + A ^ 2 * 4 = - A * (C - 4 * A) by ring] at f1
      simp [l] at f1
      nlinarith

  -- the backward direction
  . intro h
    simp [u]
    intro x' y' x y
    intro hx'
    intro hy'
    simp [hx', hy']
    clear hx' hy'
    rcases h with h | h
    .
      rcases h with ⟨ha, hb, hc⟩
      clear u
      simp [hb,hc]
      clear hb hc
      ring_nf
      constructor
      .
        intro h
        nlinarith
      .
        intro h
        nlinarith
    .
      rcases h with ⟨ha, hb, hc⟩
      clear u
      simp [hb,hc]
      clear hb hc
      ring_nf
      constructor
      .
        intro h
        nlinarith
      .
        intro h
        nlinarith
        