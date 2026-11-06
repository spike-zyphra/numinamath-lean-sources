import Mathlib

open Real Finset

-- Assume that a^2 + b^2 ≠ 0 and show that there exists x
-- such that cos x = a / √(a^2 + b^2) ∧ sin x = b / √(a^2 + b^2).
lemma lemma_1 {a b : ℝ} (h : a^2 + b^2 ≠ 0) : ∃ x, cos x = a / √(a^2 + b^2) ∧ sin x = b / √(a^2 + b^2) := by
  -- Let z = a + b * I.
  set z : Complex := a + b * .I
  -- Then ‖z‖ = √(a^2 + b^2).
  have hz : ‖z‖ = √(a^2 + b^2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq, z, pow_two]
  -- z ≠ 0 because ‖z‖ ≠ 0.
  have hz0 : z ≠ 0 := by
    contrapose! h
    simp [h] at hz
    symm at hz
    rw [sqrt_eq_zero (by positivity)] at hz
    exact hz
  -- Take x = z.arg.
  use z.arg
  -- We have cos x = z.re / ‖z‖ and sin x = z.im / ‖z‖.
  rw [Complex.cos_arg hz0, Complex.sin_arg, ← Complex.norm_eq_abs, hz]
  simp [z]

-- Assume that a^2 + b^2 ≠ 0 and show that there exists y
-- such that a * cos x - b * sin x = √(a^2 + b^2) * cos (x + y) for all x.
lemma lemma_2 {a b : ℝ} (h : a^2 + b^2 ≠ 0) : ∃ y, ∀ x, a * cos x - b * sin x = √(a^2 + b^2) * cos (x + y) := by
  -- Find y from lemma_1.
  have ⟨y, hy1, hy2⟩ := lemma_1 h
  use y
  intro x
  -- Use the formula cos(x + y) = cos x * cos y - sin x * sin y to get the result.
  rw [cos_add, hy1, hy2]
  field_simp
  ring

/- 2. Let $a_{1}, a_{2}, \ldots, a_{n} \in \mathbb{R}$ and let $f: \mathbb{R} \rightarrow \mathbb{R}$ be a function defined by
$$
f(x)=\cos \left(a_{1}+x\right)+\frac{\cos \left(a_{2}+x\right)}{2}+\frac{\cos \left(a_{3}+x\right)}{2^{2}}+\ldots+\frac{\cos \left(a_{n}+x\right)}{2^{n-1}}
$$
Prove that if $f\left(x_{1}\right)=f\left(x_{2}\right)=0$ then there exists $m \in \mathbb{Z}$ such that $x_{1}-x_{2}=m \pi$. -/
theorem algebra_216839 (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
    (f : ℝ → ℝ) (hf : ∀ x, f x = ∑ i : Fin n, Real.cos (a i + x) / 2 ^ i.val)
    (x₁ x₂ : ℝ) (hx₁ : f x₁ = 0) (hx₂ : f x₂ = 0) :
    ∃ m : ℤ, x₁ - x₂ = m * Real.pi := by
  -- It is more convenient to work with functions from ℕ → ℝ.
  -- Define a'(i) = a(i) for all i < n.
  set a' : ℕ → ℝ := fun i => if hi : i < n then a ⟨i, hi⟩ else 0
  -- Show that f(x) = ∑ i ∈ range n, cos (a' i + x) / 2 ^ i.
  replace hf x : f x = ∑ i ∈ range n, cos (a' i + x) / 2 ^ i := by
    rw [hf, sum_fin_eq_sum_range]
    apply sum_congr rfl
    simp only [mem_range]
    intro i hi
    simp [hi, a']
  -- Define A = ∑ i ∈ range n, cos (a' i) / 2 ^ i and
  ---       B = ∑ i ∈ range n, sin (a' i) / 2 ^ i.
  set A := ∑ i ∈ range n, cos (a' i) / 2 ^ i
  set B := ∑ i ∈ range n, sin (a' i) / 2 ^ i
  -- Show that f(x) = A * cos x - B * sin x.
  have eq x : f x = A * cos x - B * sin x := calc
    _ = ∑ i ∈ range n, (cos (a' i) * cos x - sin (a' i) * sin x) / 2 ^ i := by
      simp [hf, cos_add]
    _ = ∑ i ∈ range n, ((cos (a' i) / 2 ^ i) * cos x - (sin (a' i) / 2 ^ i) * sin x) := by
      apply sum_congr rfl
      intro i _
      ring
    _ = A * cos x - B * sin x := by simp [← sum_mul]
  -- Prove that A^2 + B^2 ≠ 0.
  have hab : A^2 + B^2 ≠ 0 := by
    -- Suppose that A^2 + B^2 = 0 and derive a contradiction.
    by_contra h
    -- We get A = 0 and B = 0, so f(x) = 0 for all x.
    replace h : A = 0 ∧ B = 0 := by
      constructor <;> nlinarith
    simp [h] at eq
    -- Show that |∑ i ∈ Ico 1 n, cos (a' i - a' 0) / 2 ^ i| = 1.
    have eq1 : |∑ i ∈ Ico 1 n, cos (a' i - a' 0) / 2 ^ i| = 1 := by
      -- It is enough to show that ∑ i ∈ Ico 1 n, cos (a' i - a' 0) / 2 ^ i = -1.
      rw [abs_eq zero_le_one]
      right
      -- f(-a' 0) = 0.
      have h := eq (-a' 0)
      -- 0 = f(-a' 0) = cos 0 + ∑ i ∈ Ico 1 n, cos (a' i - a' 0) / 2 ^ i.
      rw [hf, sum_range_eq_add_Ico _ hn] at h
      simp [← sub_eq_add_neg] at h
      -- cos 0 = 1, so we get ∑ i ∈ Ico 1 n, cos (a' i - a' 0) / 2 ^ i = -1.
      linarith
    -- Show that |∑ i ∈ Ico 1 n, cos (a' i - a' 0) / 2 ^ i| < 1.
    contrapose! eq1
    apply ne_of_lt
    calc
      _ ≤ ∑ i ∈ Ico 1 n, |cos (a' i - a' 0) / 2 ^ i| := by
        apply abs_sum_le_sum_abs
      -- We get
      -- |∑ i ∈ Ico 1 n, cos (a' i - a' 0) / 2 ^ i|
      --     ≤ ∑ i ∈ Ico 1 n, |cos (a' i - a' 0) / 2 ^ i|
      --     ≤ ∑ i ∈ Ico 1 n, (1 / 2) ^ i.
      _ ≤ ∑ i ∈ Ico 1 n, (1 / 2)^i := by
        apply sum_le_sum
        intro i hi
        rw [abs_div, abs_of_nonneg (a := (2 : ℝ) ^ i) (by positivity)]
        rw [div_pow, one_pow]
        gcongr
        exact abs_cos_le_one _
      -- ∑ i ∈ Ico 1 n, (1 / 2) ^ i = ((1/2)^1 - (1/2)^n) / (1 - 1/2).
      _ = ((1/2)^1 - (1/2)^n) / (1 - 1/2) := by
        rw [geom_sum_Ico' (by norm_num) (by omega)]
      -- ((1/2)^1 - (1/2)^n) / (1 - 1/2) = 1 - (1/2)^n * 2 < 1.
      _ < 1 := by
        ring_nf
        suffices 0 < (1 / 2 : ℝ)^n by linarith
        positivity
  -- Obtain y from lemma_2 such that
  -- f(x) = A * cos x - B * sin x = √(A^2 + B^2) * cos (x + y).
  have ⟨y, hy⟩ := lemma_2 hab
  -- f(x₁) = 0 and f(x₂) = 0 imply that cos(x₁ + y) = cos(x₂ + y) = 0.
  have ⟨eq1, eq2⟩ : cos (x₁ + y) = 0 ∧ cos (x₂ + y) = 0 := by
    have h1 := hy x₁
    have h2 := hy x₂
    simp [← eq, hx₁, hx₂] at h1 h2
    suffices √(A^2 + B^2) ≠ 0 by
      simp [this] at h1 h2
      exact ⟨h1, h2⟩
    positivity
  -- We get x₁ + y = (2 * k1 + 1) * π / 2 for some k1 ∈ ℤ and
  -- x₂ + y = (2 * k2 + 1) * π / 2 for some k2 ∈ ℤ.
  rw [cos_eq_zero_iff] at eq1 eq2
  have ⟨k1, hk1⟩ := eq1
  have ⟨k2, hk2⟩ := eq2
  -- Take m = k1 - k2 and show that x₁ - x₂ = m * π.
  use k1 - k2
  push_cast
  linear_combination hk1 - hk2