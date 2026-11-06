import Mathlib

open Real

/-- `f k x y` denotes that $4*x^2 - 6*k*x*y + (3*k^2+2)*y^2 - 4*x - 4*y + 6
$-/
def f_4098 (k : ℝ) x y := 4*x^2 - 6*k*x*y + (3*k^2+2)*y^2 - 4*x - 4*y + 6

/-- simplify the expression `f k x y`. -/
lemma p86' : ∀ (x y k : ℝ),
          f_4098 k x y = (x-2)^2 + 2*(y-1)^2 + 3*(x-k*y)^2 := by
  intro x y k
  dsimp [f_4098]
  nlinarith

/-- There exists a constant $k$ so that the minimum value of
\[4x^2 - 6kxy + (3k^2 + 2) y^2 - 4x - 4y + 6\]over all real numbers $x$ and $y$ is 0.  Find $k.$-/
theorem intermediate_algebra_4098 {k : ℝ} : k = 2 ↔
      (∀ (x y : ℝ), 0 ≤ f_4098 k x y) ∧ ∃ x, ∃ y, f_4098 k x y = 0 := by
  constructor
  · -- `f k x y` is nonegative when $k=2$, and exists $x$ and $y$ such that `f k x y` equal zero.
    intro hk
    constructor
    · intro x y
      rw [p86']
      nlinarith
    · use 2; use 1
      rw [p86']
      nlinarith
  · intro ⟨_,⟨x,⟨y,hf⟩⟩⟩
    rw [p86'] at hf
    -- \begin{align*}
    -- 4x^2 - 6kxy + (3k^2 + 2) y^2 - 4x - 4y + 6 &= x^2 - 4x + 4 + 2y^2 - 4y + 2 + 3x^2 - 6kxy + 3k^2 y^2 \\
    -- &= (x^2 - 4x + 4) + 2(y^2 - 2y + 1) + 3(x^2 - 2kxy + k^2 y^2) \\
    -- &= (x - 2)^2 + 2(y - 1)^2 + 3(x - ky)^2.
    -- \end{align*}
    have h₁ : 0 ≤ (x - 2) ^ 2 + 2 * (y - 1) ^ 2 := by
      nlinarith
    have h₂ : 0 ≤ 3 * (x - k * y) ^ 2 := by
      nlinarith
    have h' : (x - 2) ^ 2 + 2 * (y - 1) ^ 2 = 0 ∧ 3 * (x - k * y) ^ 2 = 0 := by
      apply (add_eq_zero_iff_of_nonneg h₁ h₂).mp hf
    have hx_eq_ky : x = k * y := by
      nlinarith
    have h'' : (x - 2) ^ 2 = 0 ∧ 2 * (y - 1) ^ 2 = 0 := by
      have h₁ : 0 ≤ (x - 2) ^ 2 := by nlinarith
      have h₂ : 0 ≤ 2 * (y - 1) ^ 2 := by
        have : 0 ≤ 2 * (y - 1) ^ 2 ↔ 0 ≤ (y - 1) ^ 2 := mul_nonneg_iff_right_nonneg_of_pos (by norm_num)
        apply this.mpr (by apply pow_two_nonneg)
      apply (add_eq_zero_iff_of_nonneg h₁ h₂).mp h'.1
    -- The only way that this expression can take on the value of 0 is if $x = 2,$ $y = 1,$ and $x = ky.$  Thus, $k = 2$.
    have hx : x = 2 := eq_of_sub_eq_zero (pow_eq_zero h''.1)
    have hy : y = 1 := eq_of_sub_eq_zero <| pow_eq_zero <| eq_zero_of_ne_zero_of_mul_left_eq_zero (by linarith) h''.2
    nlinarith
