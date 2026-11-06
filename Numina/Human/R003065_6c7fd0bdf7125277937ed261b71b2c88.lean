import Mathlib

-- Define f : ℕ → ℕ × ℕ × ℕ by
-- f(0) = (2, 1, 1)
-- f(n + 1) = (3 * y * x - z, x, y) where (x, y, z) = f(n).
def f : ℕ → ℕ × ℕ × ℕ
| 0 => ⟨2, 1, 1⟩
| n + 1 => let ⟨x, y, z⟩ := f n; ⟨3 * y * x - z, x, y⟩

-- If f(n) = (x, y, z) then 1 ≤ z ≤ y < x.
lemma lemma_1 (n : ℕ) :
    let ⟨x, y, z⟩ := f n
    x > y ∧ y ≥ z ∧ z ≥ 1 := by
  -- Proof by induction.
  induction n with
  | zero => simp [f]
  | succ n ih =>
    simp [f] at ih ⊢
    set x := (f n).1
    set y := (f n).2.1
    set z := (f n).2.2
    refine ⟨?_, by linarith, by linarith⟩
    -- It is enough to show that x + z < 3 * y * x.
    suffices x + z < 3 * y * x by omega
    -- We have x + z < 2 * x < 3 * x ≤ 3 * y * x.
    nlinarith

-- Show that (x, y, z) = f(n) is a solution of x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z.
lemma lemma_2 (n : ℕ) : f n ∈ {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z} := by
  induction n with
  | zero => simp [f]
  | succ n ih =>
    have hineq := lemma_1 n
    simp [f] at ih hineq ⊢
    set x := (f n).1
    set y := (f n).2.1
    set z := (f n).2.2
    have : z < 3 * y * x := by nlinarith
    refine ⟨this, by linarith, by linarith, ?_⟩
    have h := ih.2.2.2
    zify [this] at h ⊢
    linear_combination h

-- Show that f is strictly increasing function.
lemma lemma_3 : StrictMono f := by
  -- It is enough to show that f(n) < f(n + 1).
  apply strictMono_nat_of_lt_succ
  intro n
  -- Let f(n) = (x, y, z), f(n + 1) = (3 * y * x - z, x, y).
  have h := lemma_1 n
  simp [f] at h ⊢
  set x := (f n).1 with hx
  set y := (f n).2.1 with hy
  set z := (f n).2.2 with hz
  -- Show that x < 3 * y * x - z, y ≤ x, and z ≤ y.
  apply Prod.lt_of_lt_of_le
  · simp [← hx]
    suffices x + z < 3 * y * x by omega
    nlinarith
  simp
  rw [Prod.le_def]
  simp [← hy, ← hz]
  constructor <;> linarith

/- 18th Brazil 1996 Problem A1 Show that the equation x 2 + y 2 + z 2 = 3xyz has infinitely many solutions in positive integers. -/
theorem number_theory_150235 :
    Set.Infinite {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z} :=
  -- The function f is injective (because it is strictly increasing), so
  -- the image f '' ℕ is infinite. On the other hand, lemma_2 implies that
  -- f '' ℕ ⊆ {(x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z}.
  Set.infinite_of_injective_forall_mem lemma_3.injective lemma_2