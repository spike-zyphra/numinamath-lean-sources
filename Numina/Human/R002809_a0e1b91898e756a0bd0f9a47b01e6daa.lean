import Mathlib

open Real Filter
open scoped Topology

-- Show that A(x)^n = [(1 + cos (2 * x) ^ n) / 2, (1 - cos (2 * x) ^ n) / 2;
--                     (1 - cos (2 * x) ^ n) / 2, (1 + cos (2 * x) ^ n) / 2].
lemma lemma_1 {x : ℝ} (n : ℕ) : !![cos x ^ 2, sin x ^ 2; sin x ^ 2, cos x ^ 2] ^ n =
    !![(1 + cos (2 * x) ^ n) / 2, (1 - cos (2 * x) ^ n) / 2;
       (1 - cos (2 * x) ^ n) / 2, (1 + cos (2 * x) ^ n) / 2] := by
  -- Proof by induction
  induction n with
  | zero => simp [Matrix.one_fin_two]
  | succ n ih =>
    rw [pow_succ, ih]
    simp
    clear ih
    -- It is enough to show that
    -- (1 + cos (2 * x)^n) / 2 * cos x^2 + (1 - cos (2 * x)^n) / 2 * sin x^2
    --    = (1 + cos (2 * x)^(n + 1)) / 2 and
    -- (1 + cos (2 * x)^n) / 2 * sin x^2 + (1 - cos (2 * x)^n) / 2 * cos x^2
    --    = (1 - cos (2 * x)^(n + 1)) / 2.
    have eq1 : (1 + cos (2 * x)^n) / 2 * cos x^2 + (1 - cos (2 * x)^n) / 2 * sin x^2
                  = (1 + cos (2 * x)^(n + 1)) / 2 := calc
      _ = ((cos x^2 + sin x^2) + cos (2 * x)^n * (cos x^2 - sin x^2)) / 2 := by ring
      _ = (1 + cos (2 * x)^(n + 1)) / 2 := by
        -- The result follows from cos x^2 + sin x^2 = 1 and cos x^2 - sin x^2 = cos (2 * x).
        rw [cos_sq_add_sin_sq, ← cos_two_mul']
        ring
    have eq2 : (1 + cos (2 * x)^n) / 2 * sin x^2 + (1 - cos (2 * x)^n) / 2 * cos x^2
                  = (1 - cos (2 * x)^(n + 1)) / 2 := calc
      _ = ((sin x^2 + cos x^2) - cos (2 * x)^n * (cos x^2 - sin x^2)) / 2 := by ring
      _ = (1 - cos (2 * x)^(n + 1)) / 2 := by
        -- The result follows from sin x^2 + cos x^2 = 1 and cos x^2 - sin x^2 = cos (2 * x).
        rw [sin_sq_add_cos_sq, ← cos_two_mul']
        ring
    rw [add_comm ((1 - _) / 2 * _), add_comm ((1 - _ ) / 2 * _)]
    rw [eq1, eq2]

-- Show that det (A(x)^n) = cos (2 * x)^n.
lemma lemma_2 {x : ℝ} (n : ℕ) : (!![cos x ^ 2, sin x ^ 2; sin x ^ 2, cos x ^ 2] ^ n).det = cos (2 * x)^n := by
  -- The result follows from lemma_1 and from the determinant formula.
  rw [lemma_1, Matrix.det_fin_two_of]
  ring

-- Show that det (∑ k ∈ [1, n], A(x)^k) = n * ∑ k ∈ [1, n], cos (2 * x)^k.
lemma lemma_3 {x : ℝ} (n : ℕ) : (∑ k ∈ Finset.Icc 1 n, !![cos x ^ 2, sin x ^ 2; sin x ^ 2, cos x ^ 2] ^ k).det
    = n * ∑ k ∈ Finset.Icc 1 n, cos (2 * x)^k := by
  -- Define a = (n + ∑ k ∈ Finset.Icc 1 n, cos (2 * x)^k) / 2.
  set a := (n + ∑ k ∈ Finset.Icc 1 n, cos (2 * x)^k) / 2
  -- Define b = (n - ∑ k ∈ Finset.Icc 1 n, cos (2 * x)^k) / 2.
  set b := (n - ∑ k ∈ Finset.Icc 1 n, cos (2 * x)^k) / 2
  -- Show that ∑ k ∈ [1, n], A(x)^k = !![a, b; b, a].
  have eq : ∑ k ∈ Finset.Icc 1 n, !![cos x ^ 2, sin x ^ 2; sin x ^ 2, cos x ^ 2] ^ k = !![a, b; b, a] := by
    -- Proof by induction.
    induction n with
    | zero =>
      simp [a, b]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith), ih, lemma_1]
      simp
      set c : ℝ := (n + _) / 2 + _
      set d : ℝ := (n - _) / 2 + _
      suffices c = a ∧ d = b by rw [this.1, this.2]
      clear ih
      constructor
      · simp [a, Finset.sum_Icc_succ_top, c]
        ring
      · simp [b, Finset.sum_Icc_succ_top, d]
        ring
  -- The determinant of !![a, b; b, a] is a * a - b * b = (a - b) * (a + b).
  rw [eq, Matrix.det_fin_two_of, show a * a - b * b = (a - b) * (a + b) by ring]
  dsimp [a, b]
  -- It is easy to show that (a - b) * (a + b) = n * ∑ k ∈ [1, n], cos (2 * x)^k.
  ring

/- ## SUBJECT I

Let the matrix $A=\left(\begin{array}{cc}\cos ^{2} x & \sin ^{2} x \\ \sin ^{2} x & \cos ^{2} x\end{array}\right), x \in \mathbb{R}$

a) Show that $A^{n}=\left(\begin{array}{ll}\frac{1+\cos ^{n} 2 x}{2} & \frac{1-\cos ^{n} 2 x}{2} \\ \frac{1-\cos ^{n} 2 x}{2} & \frac{1+\cos ^{n} 2 x}{2}\end{array}\right)$, for any non-zero natural number $n$.

b) Calculate $\lim _{x \rightarrow \infty} \frac{\sum_{k=1}^{n} \operatorname{det} A^{k}}{\operatorname{det}\left(\sum_{k=1}^{n} A^{k}\right)}$. -/
theorem algebra_116589 {x : ℝ} (A : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hA : A = λ x => !![cos x ^ 2, sin x ^ 2; sin x ^ 2, cos x ^ 2])
    (n : ℕ) (hn : n ≠ 0) :
    A x ^ n = !![(1 + cos (2 * x) ^ n) / 2, (1 - cos (2 * x) ^ n) / 2;
                 (1 - cos (2 * x) ^ n) / 2, (1 + cos (2 * x) ^ n) / 2] ∧
    Tendsto (fun x => (∑ k ∈ Finset.Icc 1 n, (A x ^ k).det) / (∑ k ∈ Finset.Icc 1 n, A x ^ k).det) (atTop ⊓ 𝓟 {x | ∑ k ∈ Finset.Icc 1 n, cos (2 * x) ^ k ≠ 0}) (𝓝 (1 / n)) := by
  constructor
  -- The formula for A x ^ n follows from lemma_1.
  · rw [hA, lemma_1]
  -- Show that (∑ k ∈ [1, n], (A x ^ k).det) / (∑ k ∈ [1, n], A x ^ k).det) = 1 / n
  -- for all x such that ∑ k ∈ [1, n], cos (2 * x) ^ k ≠ 0.
  have eq : (fun x : ℝ => (1 : ℝ) / n) =ᶠ[atTop ⊓ 𝓟 {x | ∑ k ∈ Finset.Icc 1 n, cos (2 * x) ^ k ≠ 0}] (fun x => (∑ k ∈ Finset.Icc 1 n, (A x ^ k).det) / (∑ k ∈ Finset.Icc 1 n, A x ^ k).det) := by
    simp_rw [EventuallyEq, eventually_iff_exists_mem]
    use {x | ∑ k ∈ Finset.Icc 1 n, cos (2 * x) ^ k ≠ 0}
    simp only [mem_inf_principal, Set.mem_setOf_eq, imp_self, Set.setOf_true, univ_mem, true_and]
    intro y hy
    -- The result follows from lemma_2 and lemma_3.
    simp only [hA, lemma_3, lemma_2]
    rw [div_mul_cancel_right₀ hy, one_div]
  apply Tendsto.congr' eq
  -- The limit of fun x => 1 / n is equal to 1 / n.
  apply tendsto_const_nhds