import Mathlib

open Real

-- Define f 0 x = x, f (n + 1) x = 1 + 1 / f n x.
noncomputable def f (n : ℕ) (x : ℝ) : ℝ :=
  match n with
  | 0 => x
  | n + 1 => 1 + 1 / f n x

-- If f i x ≠ 0 for all i ≤ n then
-- f (n + 1) x = ((n + 2).fib * x + (n + 1).fib) / ((n + 1).fib * x + n.fib).
lemma f_eq {n x} (h : ∀ i ≤ n, f i x ≠ 0) : f (n + 1) x = ((n + 2).fib * x + (n + 1).fib) / ((n + 1).fib * x + n.fib) := by
  -- Proof by induction.
  induction n with
  | zero =>
    -- f (0 + 1) x = f 1 x = 1 + 1 / x = (x + 1) / x = (fib 2 * x + fib 1) / (fib 1 * x + fib 0).
    have := h 0
    simp [f] at this
    field_simp [f]
  | succ n ih =>
    -- We have f (n + 1) x = (fib (n + 2) * x + fib (n + 1)) / (fib (n + 1) * x + fib n).
    -- Show that f (n + 2) x = (fib (n + 3) * x + fib (n + 2)) / (fib (n + 2) * x + fib (n + 1)).
    replace ih := ih (fun i hi => h i (by omega))
    -- f (n + 2) = 1 + 1 / f (n + 1) x = 1 + (fib (n + 1) * x + fib n) / (fib (n + 2) * x + fib (n + 1)).
    rw [f, ih]
    -- We have fib (n + 2) * x + fib (n + 1) ≠ 0.
    have h0 : (n + 2).fib * x + (n + 1).fib ≠ 0 := by
      -- If fib (n + 2) * x + fib (n + 1) = 0 then f (n + 1) x = 0, a contradiction
      -- with the assumption f i x ≠ 0 for all i ≤ n + 1.
      contrapose! h
      use n + 1, le_refl _
      simp [ih, h]
    field_simp
    -- The result follows from fib (n + 3) = fib (n + 2) + fib (n + 1) and
    -- fib (n + 2) = fib (n + 1) + fib n.
    calc
      _ = ((n + 1).fib + (n + 2).fib : ℕ) * x + (n.fib + (n + 1).fib : ℕ) := by push_cast; ring
      _ = (n + 1 + 2).fib * x + (n + 1 + 1).fib := by
        rw [show n + 2 = (n + 1) + 1 by ring, ← Nat.fib_add_two, ← Nat.fib_add_two]

-- If f n x = 0 then 1 ≤ f i x for all i > n.
lemma f_ge_one_of_eq_zero {n x} (h : f n x = 0) : ∀ i > n, 1 ≤ f i x := by
  intro i hi
  -- Proof by induction.
  induction i with
  | zero => simp at hi
  | succ i ih =>
    -- Assume that 1 ≤ f i x if i > n. Show that 1 ≤ f (i + 1) x for i + 1 > n.
    -- Consider two cases: i = n or i > n.
    cases' show i = n ∨ i > n by omega with hi2 hi2
    · -- If i = n then f (i + 1) x = f (n + 1) x = 1 + 1 / f n x = 1 + 1 / 0 = 1.
      rw [f, hi2, h]
      norm_num
    · -- If i > n then f (i + 1) x = 1 + 1 / f i x ≥ 1 (since f i x ≥ 1).
      simp [f]
      linarith [ih hi2]

-- If f n x = 0 then fib (k + 1) * x + fib k = 0 for some k.
lemma f_eq_zero {n x} (h0 : f n x = 0) : ∃ k, (k + 1).fib * x + k.fib = 0 := by
  cases' n with n
  · -- If n = 0 then f 0 x = 0 implies x = 0.
    simp [f] at h0
    -- We get fib 1 * x + fib 0 = 0.
    use 0
    simp [h0]
  -- Assume now that n = n' + 1 ≠ 0.
  -- Show that f i x ≠ 0 for all i ≤ n.
  have h : ∀ i ≤ n, f i x ≠ 0 := by
    -- Assume that f i x = 0 for some i ≤ n' and show that f (n' + 1) x ≠ 0.
    contrapose! h0
    have ⟨i, hi, heq⟩ := h0
    -- f i x = 0 implies that f k x ≥ 1 for all k > i.
    -- In particular, f (n' + 1) x ≥ 1 > 0.
    linarith [f_ge_one_of_eq_zero heq (n + 1) (by linarith)]
  -- f i x ≠ 0 for all i ≤ n implies that
  -- f (n' + 1) x = (fib (n' + 2) * x + fib (n' + 1)) / (fib (n' + 1) * x + fib n').
  -- This expression is equal to 0 iff
  -- fib (n' + 2) * x + fib (n' + 1) = 0 or fib (n' + 1) * x + fib n' = 0.
  simp [f_eq h] at h0
  cases' h0 with h0 h0
  · use n + 1
  · use n

-- If f n x = 0 then x ≤ 0.
lemma le_zero_of_f_eq_zero {n x} (h0 : f n x = 0) : x ≤ 0 := by
  -- We have fib (k + 1) * x + fib k = 0 for some k.
  have ⟨k, hk⟩ := f_eq_zero h0
  -- fib (k + 1) > 0 and fib k ≥ 0, so x ≤ 0.
  suffices 0 < (k + 1).fib by
    rify at this
    nlinarith
  rw [Nat.fib_pos]
  linarith

-- If f n x = 0 then x is rational.
lemma ne_irrational_of_f_eq_zero {n x} (h0 : f n x = 0) : ¬ Irrational x := by
  -- We have fib (k + 1) * x + fib k = 0 for some k, so
  -- x is rational.
  have ⟨k, hk⟩ := f_eq_zero h0
  apply_fun Irrational at hk
  simp at hk
  exact hk

-- If f (n + 1) x = x then f i x ≠ 0 for all i ≤ n.
lemma f_ne_zero_of_eq_x {n x} (h : f (n + 1) x = x) : ∀ i ≤ n, f i x ≠ 0 := by
  -- Assume that f i x = 0 for some i ≤ n.
  -- Show that fib (n + 1) x ≠ x.
  contrapose! h
  have ⟨i, hi, heq⟩ := h
  -- le_zero_of_f_eq_zero and f i x = 0 imply that x ≤ 0.
  have hx1 := le_zero_of_f_eq_zero heq
  -- f_ge_one_of_eq_zero, f i x = 0, and n + 1 > i imply that 1 ≤ f (n + 1) x.
  have hx2 := f_ge_one_of_eq_zero heq (n + 1) (by linarith)
  -- We get x ≤ 0 < 1 ≤ f (n + 1) x, so f (n + 1) x ≠ x.
  apply ne_of_gt
  linarith

-- Show that x * x - x - 1 = 0 iff x = (1 + √5) / 2 ∨ x = (1 - √5) / 2.
lemma lemma_1 {x} : (x * x - x - 1 = 0) ↔ x = (1 + √5) / 2 ∨ x = (1 - √5) / 2 := by
  rw [show x * x - x - 1 = 1 * (x * x) + (-1) * x + (-1) by ring]
  rw [quadratic_eq_zero_iff (s := √5) one_ne_zero, mul_one, neg_neg]
  simp [discrim]
  norm_num

-- If x * x - x - 1 = 0 then f i x ≠ 0 for all i.
lemma lemma_2 {x} (h : x * x - x - 1 = 0) : ∀ i, f i x ≠ 0 := by
  -- We have x = (1 + √5) / 2 ∨ x = (1 - √5) / 2
  have hroots := lemma_1.mp h
  -- Assume that f n x = 0 for some n and derive a contradiction.
  contrapose! hroots
  have ⟨n, hn⟩ := hroots
  -- f n x = 0 implies that x is rational.
  have := ne_irrational_of_f_eq_zero hn
  -- It is left to show that (1 + √5) / 2 and (1 - √5) / 2 are irrational.
  contrapose! this
  have h5 : Irrational √5 := by
    apply Nat.prime_five.irrational_sqrt
  by_cases hx : x = (1 + √5) / 2
  · simp [hx]
    apply Irrational.div_nat _ (by norm_num)
    rw [show (1 : ℝ) = (1 : ℕ) by simp]
    apply Irrational.nat_add h5
  · simp [this hx]
    apply Irrational.div_nat _ (by norm_num)
    rw [show (1 : ℝ) = (1 : ℕ) by simp]
    apply Irrational.nat_sub h5

/- Solve the equation
$$
1+\frac{1}{1+\frac{1}{1+\ddots{ }_{1}+\frac{1}{x}}}=x \quad(n \text { layers }) .
$$
 -/
theorem algebra_113307 {x : ℝ} {n : ℕ} :
    f (n + 1) x = x ↔ x = (1 + √5) / 2 ∨ x = (1 - √5) / 2 := calc
  -- f (n + 1) x = x implies that f i x ≠ 0 for all i ≤ n (f_ne_zero_of_eq_x).
  f (n + 1) x = x ↔ f (n + 1) x = x ∧ ∀ i ≤ n, f i x ≠ 0 := by
    simp only [ne_eq, iff_self_and]
    intro h
    apply f_ne_zero_of_eq_x h
  -- f (n + 1) x = x is equivalent to (n + 1).fib * (x * x - x - 1) = 0.
  _ ↔ (n + 1).fib * (x * x - x - 1) = 0 ∧ ∀ i ≤ n, f i x ≠ 0 := by
    simp only [ne_eq, one_mul, neg_mul, and_congr_left_iff]
    intro h0
    -- We have f i x ≠ 0 for all i ≤ n, so
    -- f (n + 1) x =  (fib (n + 2) * x + fib (n + 1)) / (fib (n + 1) * x + fib n).
    rw [f_eq h0]
    -- Show that fib (n + 1) * x + fib n ≠ 0.
    have hne0 : (n + 1).fib * x + n.fib ≠ 0 := by
      by_cases hn0 : n = 0
      · -- If n = 0 then fib (n + 1) * x + fib n = x.
        simp [hn0]
        -- x ≠ 0 because f 0 x = x ≠ 0.
        have := h0 0 (by simp)
        simp [f] at this
        exact this
      -- Assume that n ≠ 0.
      -- Then we have f n x = f (n - 1 + 1) x = (fib (n + 1) * x + fib n) / (fib n * x + fib (n - 1)).
      have eq := f_eq (n := n - 1) (fun i hi => h0 i (by omega))
      rw [show n - 1 + 1 = n by omega, show n - 1 + 2 = n + 1 by omega] at eq
      -- We know that f n x ≠ 0, so fib (n + 1) * x + fib n ≠ 0.
      contrapose! h0
      use n, le_refl _
      simp [eq, h0]
    -- Simplify the expression f (n + 1) x = x and get the result from
    -- fib (n + 2) = fib (n + 1) + fib n.
    field_simp
    rw [Nat.fib_add_two]
    push_cast
    constructor <;> intros <;> linarith
  -- Show that fib (n + 1) * (x * x - x - 1) = 0 ∧ ∀ i ≤ n, f i x ≠ 0
  -- is equivalent to x = (1 + √5) / 2 ∨ x = (1 - √5) / 2.
  _ ↔ x = (1 + √5) / 2 ∨ x = (1 - √5) / 2 := by
    -- lemma_1 implies that x = (1 + √5) / 2 ∨ x = (1 - √5) / 2 is
    -- equivalent to x * x - x - 1 = 0.
    rw [← lemma_1]
    simp only [mul_eq_zero, Nat.cast_eq_zero, Nat.fib_eq_zero, AddLeftCancelMonoid.add_eq_zero,
      one_ne_zero, and_false, false_or, ne_eq, and_iff_left_iff_imp]
    -- It is left to prove that ∀ i ≤ n, f i x ≠ 0 assuming that x * x - x - 1 = 0.
    intro h i hi
    -- The result follows from lemma_2.
    apply lemma_2 h