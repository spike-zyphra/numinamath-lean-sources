import Mathlib

open Real Set

-- Show that (∑ i, a i)^2 ≤ n * ∑ i, (a i)^2 for all a.
lemma lemma_1 {n : ℕ} (a : Fin n → ℝ) : (∑ i, a i)^2 ≤ n * ∑ i, (a i)^2 := calc
  _ = (∑ i, 1 * (a i))^2 := by simp
  -- Apply the Cauchy-Schwartz inequality to (∑ i, 1 * (a i))^2.
  _ ≤ (∑ (i : Fin n), 1^2) * (∑ i, a i^2) := by
    apply Finset.sum_mul_sq_le_sq_mul_sq
  -- We have (∑ (i : Fin n), 1^2) = n and the result follows.
  _ = n * ∑ i, (a i)^2 := by simp

-- Show that (∑ i, a i)^4 ≤ n^3 * ∑ i, (a i)^4 for all a.
lemma lemma_2 {n : ℕ} (a : Fin n → ℝ) : (∑ i, a i)^4 ≤ n^3 * ∑ i, (a i)^4 := calc
  _ = ((∑ i, a i)^2)^2 := by rw [← pow_mul]
  -- Apply lemma_1 to (∑ i, a i)^2 and get
  -- ((∑ i, a i)^2)^2 ≤ n^2 * (∑ i, a i^2)^2.
  _ ≤ (n * ∑ i, a i^2)^2 := by
    gcongr
    apply lemma_1
  _ = n^2 * (∑ i, a i^2)^2 := by rw [mul_pow]
  -- Apply lemma_1 to (∑ i, a i^2)^2 and get the result.
  _ ≤ n^2 * (n * ∑ i, (a i^2)^2) := by
    gcongr
    apply lemma_1
  _ = n^3 * ∑ i, a i^4 := by
    simp_rw [← mul_assoc, ← pow_succ, ← pow_mul]

-- Show that a^2 * b^2 ≤ (1 / 2) * (a^4 + b^4) for all a and b.
lemma lemma_3 (a b : ℝ) : a^2 * b^2 ≤ (1 / 2) * (a^4 + b^4) := by
  linarith [sq_nonneg (a^2 - b^2)]

/- 3. Given numbers $x_{1}, \ldots, x_{n}$ from the interval $\left[0, \frac{\pi}{2}\right]$. Find the maximum value of the expression
$$
A=\left(\sqrt{\sin x_{1}}+\ldots+\sqrt{\sin x_{n}}\right) \cdot\left(\sqrt{\cos x_{1}}+\ldots+\sqrt{\cos x_{n}}\right) .
$$
 -/
theorem inequalities_220049 {n : ℕ} (hn : 0 < n) :
    IsGreatest {a | ∃ x : Fin n → ℝ,
      (∀ i, x i ∈ Icc 0 (π/2)) ∧
      a = (∑ i, √(sin (x i))) * (∑ i, √(cos (x i)))} (n^2 / sqrt 2) := by
  simp only [IsGreatest, mem_Icc, mem_setOf_eq, upperBounds, forall_exists_index, and_imp]
  constructor
  -- Show that there exists x such that the expression achieves the bound n^2 / √2.
  -- Take x(i) = π / 4 for all i.
  · use fun i => π / 4
    simp
    constructor
    · intros; constructor <;> linarith [pi_pos]
    field_simp
    ring_nf
    simp
    ring_nf
    simp
  -- Show that s = (∑ i, √(sin (x i))) * (∑ i, √(cos (x i))) ≤ n^2 / √2 for any x
  -- such that 0 ≤ x(i) ≤ π / 2.
  intro s x hx eq
  -- It is enough to show that s^2 ≤ n^4 / 2 (because 0 ≤ s).
  rw [← sq_le_sq₀ (by rw [eq]; positivity) (by positivity)]
  rw [eq, mul_pow]
  calc
    -- We get s^2 ≤ (1 / 2) * ((∑ i, √(sin (x i)))^4 + (∑ i, √(cos (x i)))^4)
    -- from lemma_3.
    _ ≤ (1 / 2) * ((∑ i, √(sin (x i)))^4 + (∑ i, √(cos (x i)))^4) := by
      apply lemma_3
    -- We get (∑ i, √(sin (x i)))^4 ≤ n^3 * ∑ i, √(sin (x i))^4
    -- and (∑ i, √(cos (x i)))^4 ≤ n^3 * ∑ i, √(cos (x i))^4
    -- from lemma_2.
    _ ≤ (1 / 2) * (n^3 * ∑ i, √(sin (x i))^4 + n^3 * ∑ i, √(cos (x i))^4) := by
      gcongr <;> apply lemma_2
    -- The last expression simplifies to
    -- (1 / 2) * n^3 * ∑ i, (sin (x i)^2 + cos (x i)^2)
    -- (because 0 ≤ sin (x i) and 0 ≤ cos (x i)).
    _ = (1 / 2) * n^3 * ∑ i, (sin (x i)^2 + cos (x i)^2) := by
      rw [← mul_add, ← Finset.sum_add_distrib, mul_assoc]
      congr
      ext i
      simp_rw [show ∀ x : ℝ, x^4 = (x^2)^2 by simp [← pow_mul]]
      have ⟨h1, h2⟩ := hx i
      rw [sq_sqrt (sin_nonneg_of_nonneg_of_le_pi h1 (by linarith))]
      rw [sq_sqrt (cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h2)]
    -- sin (x i)^2 + cos (x i)^2 = 1 so we get
    -- (1 / 2) * n^3 * n = n^4 / 2.
    _ = (1 / 2) * n^3 * n := by
      simp
    _ = (n^2 / √2)^2 := by
      simp [div_pow]
      ring