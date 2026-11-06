import Mathlib

/-Let f be function defined from the set {(x,y):x,y reals, xy≠0}
in to the set of all positive real numbers such that
(i) f(xy,z)=f(x,z)f(y,z), for all x,y≠0
(ii) f(x,yz)=f(x,y)f(x,z), for all x,y≠0
(iii)f(x,1−x)=1, for all x≠0, 1
prove that
(a) f(x, x) = f(x, -x) = 1 for all x ≠ 0
(b) f(x, y)f(y, x) = 1 for all x, y≠ 0
-/

theorem algebra_127100 {f: ℝ × ℝ → ℝ} (pf: ∀ x y, 0 < f (x, y))
  (h1: ∀ x y z, x ≠ 0 ∧ y ≠ 0 → f (x * y, z) = f (x, z) * f (y, z))
  (h2: ∀ x y z, x ≠ 0 ∧ y ≠ 0 → f (x, y * z) = f (x, y) * f (x, z))
  (h3: ∀ x, x ≠ 0 ∧ x ≠ 1 → f (x, 1 - x) = 1):
  (∀ x, x ≠ 0 → f (x, x) = 1 ∧ f (x, -x) = 1) ∧
  ∀ x y, x ≠ 0 ∧ y ≠ 0 → f (x, y) * f (y, x) = 1 := by

  -- we show that f(1,z) = 1
  have g1: ∀ z, z ≠ 0 → f (1, z) = 1 := by
    intro z hz
    specialize h1 1 1 z (by norm_num)
    norm_num at h1
    specialize pf 1 z
    set p:= f (1, z)
    replace h1: p * (p - 1) = 0 := by nlinarith
    simp at h1
    rcases h1 with i | i
    .
      simp [i] at pf
    .
      linarith

  -- simimalrly we show that f(-1,z) = 1
  have g2: ∀ z, z ≠ 0 → f (-1, z) = 1 := by
    intro z hz
    specialize h1 (-1) (-1) z (by norm_num)
    norm_num at h1
    specialize pf (-1) z
    set p:= f (-1, z)
    specialize g1 z hz
    simp [g1] at h1
    replace h1: (p + 1) * (p - 1) = 0 := by nlinarith
    simp at h1
    rcases h1 with i | i
    .
      linarith
    .
      linarith

  -- similarly, we have f (z, 1) = 1
  have g3: ∀ z, z ≠ 0 → f (z, 1) = 1 := by
    intro z hz
    specialize h2 z 1 1 (by simp [hz])
    norm_num at h2
    specialize pf z 1
    set p:= f (z, 1)
    replace h2: p * (p - 1) = 0 := by nlinarith
    simp at h2
    rcases h2 with i | i
    .
      linarith
    .
      linarith

  -- simalarly we show that f (z, -1) = 1
  have g4: ∀ z, z ≠ 0 → f (z, -1) = 1 := by
    intro z hz
    specialize h2 z (-1) (-1) (by simp [hz])
    norm_num at h2
    specialize pf z (-1)
    set p:= f (z, -1)
    specialize g3 z hz
    simp [g3] at h2
    replace h2: (p + 1) * (p - 1) = 0 := by nlinarith
    simp at h2
    rcases h2 with i | i
    .
      linarith
    .
      linarith

  have g5: ∀ x y, x ≠ 0 ∧ y ≠ 0 → f (x, 1 / y) = f (1 / x, y) ∧ f (1 / x, y) = 1 / f (x, y) := by
    intro x y h
    rcases h with ⟨hx, hy⟩
    specialize h1 (1 / x) x y
    simp [hx] at h1
    specialize g1 y hy
    simp [g1] at h1
    field_simp at h1
    specialize h2 x (1 / y) y
    simp [hx, hy] at h2
    specialize g3 x (by simp [hx])
    simp [g3] at h2
    field_simp at h2
    specialize pf x y
    replace h1: f (1 / x, y) = 1 / f (x, y) := by
      field_simp
      linarith
    replace h2: f (x, 1 / y) = 1 / f (x, y) := by
      field_simp
      linarith
    constructor
    .
      rw [h1, h2]
    .
      exact h1

  -- then we show that 1 = f (x, -x)
  have g6: ∀ x, x ≠ 0 ∧ x ≠ 1 → 1 = f (x, -x) := by
    intro x hx
    have h3':= h3
    specialize h3 (1 / x)
    have o1: 1 / x ≠ 0 := by
      by_contra! o
      simp at o
      simp [o] at hx
    have o2: 1 / x ≠ 1 := by
      by_contra! o
      simp at o
      simp [o] at hx
    simp [o1, o2, hx] at h3
    have g5':= g5
    specialize g5 x (1 - 1 / x)
    simp [hx] at g5
    have o3: 1 - x⁻¹ ≠ 0 := by
      by_contra! o
      field_simp at o
      absurd o2
      linarith
    simp [o3] at g5
    rcases g5 with ⟨i, j⟩
    rw [j] at h3
    specialize h3' x (by simp [hx])
    have o4:= pf x (1 - 1 / x)
    replace h3: f (x, 1 - x⁻¹) = 1 := by
      field_simp at h3
      field_simp
      rw [← h3]
    specialize g5' x (1 / (1 - 1 / x))
    simp [hx, o3] at g5'
    rcases g5' with ⟨k, l⟩
    rw [l] at k
    clear l
    rw [h3] at k
    field_simp at k
    specialize pf x (1 / (1 - 1 / x))
    field_simp at k
    have o: 1 / (1 - 1 / x) = -x / (1 - x) := by
      have r1: 1 - x ≠ 0 := by
        by_contra! o
        replace o: x = 1 := by linarith
        simp [o] at hx
      have r2: 1 - 1 / x ≠ 0 := by
        simp
        exact o3
      have r3: x ≠ 0 := by
        apply hx.1
      have r4: x - 1 ≠ 0 := by
        by_contra! o
        replace o: x = 1 := by linarith
        simp [o] at hx
      field_simp
      ring
    rw [o] at k
    clear o
    replace k: f (x, -x / (1 - x)) * f (x, 1 - x) = 1 := by
      rw [h3', k]
      norm_num
    specialize h2 x (-x / (1 - x)) (1 - x)
    simp [hx] at h2
    have o5: 1 - x ≠ 0 := by
      by_contra! o
      replace o: x = 1 := by linarith
      simp [o] at hx
    simp [o5] at h2
    rw [← h2] at k
    rw [k]

  -- use g6, we can show that f (x, x) = 1
  have g7: ∀ x, x ≠ 0 → f (x, x) = 1 := by
    intro x hx
    specialize g6 x
    specialize h2 x (-x) (-1) (by simp [hx])
    simp at h2
    rw [h2]
    specialize g4 x (by simp [hx])
    simp [g4]
    by_cases r: x = 1
    .
      simp [r]
      specialize g1 (-1) (by simp [hx])
      exact g1
    .
      simp [r, hx] at g6
      rw [g6]

  -- then we can show the first argument
  constructor
  .
    intro x hx
    specialize g7 x hx
    simp [g7]
    by_cases r: x = 1
    .
      simp [r]
      specialize g1 (-1) (by simp [hx])
      exact g1
    .
      specialize g6 x
      simp [r, hx] at g6
      rw [g6]

  -- finally, we show the second argument
  .
    intro x y hx
    rcases hx with ⟨hx, hy⟩
    have t:= g7
    specialize g7 (x * y)
    have o: x * y ≠ 0 := by
      by_contra! o
      simp at o
      simp [hx, hy] at o
    simp [o] at g7
    specialize h1 x y (x * y)
    simp [hx, hy] at h1
    rw [h1] at g7
    have u1:= h2 x x y
    simp [hx] at u1
    have u2:= h2 y x y
    simp [hx, hy] at u2
    simp [u1, u2] at g7
    have t1:= t x hx
    have t2:= t y hy
    simp [t1, t2] at g7
    rw [g7]